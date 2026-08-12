import ResearchLean.AG.UniformInvariance.ConditionCAllAChecker
import ResearchLean.AG.UniformInvariance.ConditionCAllABridge
import ResearchLean.AG.UniformInvariance.UniformPresentationDecider
import Formal.Util.AssertStandardAxioms

/-!
# A uniform comparison outside the C3 locus

This module formalizes the exact `C3_not_necessary` fixture from the bounded
R1 necessity map for `G-107-aat-uniform-invariance-characterization`.  The raw
presentation is copied field by field from the deterministic R1 payload: its
parent payload has SHA-256
`ff2d9fa12eb64bf343d3148f081e1164d4216d8548e53d90550eb53886dd359a`,
and the canonical serializer recomputes semantic SHA-256
`9bbb58959ac5840b3a50befbf3132fcf0b2e7dbaf41f91695c406a8c15ec5cc0`.

The coarse and fine nerves have the same three charts, three edges, and one
face, and the cell maps are identities.  Their support tables differ exactly
by the proper reading factor `Fin 3 -> Fin 2`.  Target zero selects an isolated
self-loop and no face.  Consequently its nonzero loop is a fiber cycle that
cannot be an internal-face boundary, although every selected-subset H1
comparison is bijective.

The finite presentation stores only raw readings, incidence, support, and
partial cell maps.  It stores no factor, matrix, rank, cohomology class,
defect, condition result, checker result, or uniformity certificate.  The R1
experiment is provenance for the table, not a premise of any Lean proof.
-/

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology TwoPhase

namespace R1ConditionC3Witness

/-! ## Exact raw R1 presentation -/

/-- The proper coarse reading table `[0, 0, 1]`. -/
def coarseRead (source : Fin 3) : Fin 2 :=
  if source = 2 then 1 else 0

/-- Left endpoints of the three edges `(0,0)`, `(1,2)`, and `(2,2)`. -/
def edgeLeft (edge : Fin 3) : Fin 3 :=
  if edge = 1 then 1 else if edge = 2 then 2 else 0

/-- Right endpoints of the three edges `(0,0)`, `(1,2)`, and `(2,2)`. -/
def edgeRight (edge : Fin 3) : Fin 3 :=
  if edge = 1 then 2 else if edge = 2 then 2 else 0

/-- The first edge of the unique face boundary `(1,1,2)`. -/
def faceEdge0 (_face : Fin 1) : Fin 3 := 1

/-- The second edge of the unique face boundary `(1,1,2)`. -/
def faceEdge1 (_face : Fin 1) : Fin 3 := 1

/-- The third edge of the unique face boundary `(1,1,2)`. -/
def faceEdge2 (_face : Fin 1) : Fin 3 := 2

/-- Coarse supports `{0}`, `{1}`, `{1}` on charts zero, one, and two. -/
def coarseChartSupport (chart : Fin 3) : Finset (Fin 2) :=
  if chart = 0 then {0} else {1}

/-- Fine supports `{0,1}`, `{2}`, `{2}` on charts zero, one, and two. -/
def fineChartSupport (chart : Fin 3) : Finset (Fin 3) :=
  if chart = 0 then {0, 1} else {2}

/-- The exact finite raw presentation underlying the R1 C3 witness. -/
def presentation : FiniteComparisonPresentation where
  Source := Fin 3
  sourceFintype := inferInstance
  sourceDecidableEq := inferInstance
  sourceDefault := 0
  sourceEntries := [0, 1, 2]
  source_mem_sourceEntries := by
    intro source
    fin_cases source <;> simp
  CoarseTarget := Fin 2
  coarseTargetFintype := inferInstance
  coarseTargetDecidableEq := inferInstance
  coarseTargetEntries := [0, 1]
  coarseTarget_mem_coarseTargetEntries := by
    intro target
    fin_cases target <;> simp
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
  CoarseEdge := Fin 3
  coarseEdgeFintype := inferInstance
  coarseEdgeDecidableEq := inferInstance
  CoarseFace := Fin 1
  coarseFaceFintype := inferInstance
  coarseFaceDecidableEq := inferInstance
  coarseEdgeLeft := edgeLeft
  coarseEdgeRight := edgeRight
  coarseFaceEdge0 := faceEdge0
  coarseFaceEdge1 := faceEdge1
  coarseFaceEdge2 := faceEdge2
  coarseFaceEdge0_left := by
    intro face
    fin_cases face
    simp [edgeLeft, faceEdge0, faceEdge1]
  coarseFaceEdge0_right := by
    intro face
    fin_cases face
    simp [edgeRight, edgeLeft, faceEdge0, faceEdge2]
  coarseFaceEdge1_right := by
    intro face
    fin_cases face
    simp [edgeRight, faceEdge1, faceEdge2]
  coarseChartSupport := coarseChartSupport
  coarseChartSupport_nonempty := by
    intro chart
    fin_cases chart <;> simp [coarseChartSupport]
  FineChart := Fin 3
  fineChartFintype := inferInstance
  fineChartDecidableEq := inferInstance
  FineEdge := Fin 3
  fineEdgeFintype := inferInstance
  fineEdgeDecidableEq := inferInstance
  FineFace := Fin 1
  fineFaceFintype := inferInstance
  fineFaceDecidableEq := inferInstance
  fineEdgeLeft := edgeLeft
  fineEdgeRight := edgeRight
  fineFaceEdge0 := faceEdge0
  fineFaceEdge1 := faceEdge1
  fineFaceEdge2 := faceEdge2
  fineFaceEdge0_left := by
    intro face
    fin_cases face
    simp [edgeLeft, faceEdge0, faceEdge1]
  fineFaceEdge0_right := by
    intro face
    fin_cases face
    simp [edgeRight, edgeLeft, faceEdge0, faceEdge2]
  fineFaceEdge1_right := by
    intro face
    fin_cases face
    simp [edgeRight, faceEdge1, faceEdge2]
  fineChartSupport := fineChartSupport
  fineChartSupport_nonempty := by
    intro chart
    fin_cases chart <;> simp [fineChartSupport]
  chartMap := id
  edgeMap := some
  faceMap := some
  edge_some_left := by
    intro fineEdge coarseEdge hmap
    have heq : fineEdge = coarseEdge := Option.some.inj hmap
    subst coarseEdge
    rfl
  edge_some_right := by
    intro fineEdge coarseEdge hmap
    have heq : fineEdge = coarseEdge := Option.some.inj hmap
    subst coarseEdge
    rfl
  edge_none_fiber := by
    intro fineEdge hmap
    simp at hmap
  face_some_edge0 := by
    intro fineFace coarseFace hmap
    have heq : fineFace = coarseFace := Option.some.inj hmap
    subst coarseFace
    rfl
  face_some_edge1 := by
    intro fineFace coarseFace hmap
    have heq : fineFace = coarseFace := Option.some.inj hmap
    subst coarseFace
    rfl
  face_some_edge2 := by
    intro fineFace coarseFace hmap
    have heq : fineFace = coarseFace := Option.some.inj hmap
    subst coarseFace
    rfl
  face_none_edge0 := by
    intro fineFace hmap
    simp at hmap
  face_none_edge1 := by
    intro fineFace hmap
    simp at hmap
  face_none_edge2 := by
    intro fineFace hmap
    simp at hmap
  chartSupport_compatible_source := by
    intro fineChart source hsource
    fin_cases fineChart <;> fin_cases source <;>
      simp [fineChartSupport, coarseChartSupport, coarseRead] at hsource ⊢

/-! ## Canonical factor and named target subsets -/

/-- The factor computed from the source enumeration is the raw table
`[0,0,1]`; no factor is stored in the presentation. -/
theorem computedFactor_eq_coarseRead :
    presentation.computedFactor = coarseRead := by
  funext target
  fin_cases target <;>
    decide

/-- The canonical semantic comparison factor is the same proper factor
`[0,0,1]`, by uniqueness from the raw reading tables. -/
theorem comparisonFactor_eq_coarseRead :
    comparisonFactor presentation.coarseReading presentation.fineReading
      presentation.coarserThan = coarseRead := by
  rw [← presentation.computedFactor_eq_comparisonFactor]
  exact computedFactor_eq_coarseRead

/-- The singleton coarse target on which the unfilled self-loop is selected. -/
def targetZero : Finset (Fin 2) := {0}

/-- The singleton coarse target carrying the contractible face component. -/
def targetOne : Finset (Fin 2) := {1}

/-- The full two-point coarse target set. -/
def targetFull : Finset (Fin 2) := Finset.univ

/-- Target zero is a nonempty semantic subset. -/
theorem targetZero_nonempty :
    (↑targetZero : Set (Fin 2)).Nonempty := by
  exact ⟨0, by simp [targetZero]⟩

/-- The executable preimage of target zero is exactly the two fine targets
zero and one. -/
theorem finePreimage_targetZero :
    presentation.finePreimageFinset targetZero =
      ({0, 1} : Finset (Fin 3)) := by
  ext target
  simp only [FiniteComparisonPresentation.finePreimageFinset,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [computedFactor_eq_coarseRead]
  fin_cases target <;> decide

/-- Membership in every executable fine preimage is computed by the raw
proper factor. -/
theorem mem_finePreimage_iff (A : Finset (Fin 2)) (target : Fin 3) :
    target ∈ presentation.finePreimageFinset A ↔ coarseRead target ∈ A := by
  simp only [FiniteComparisonPresentation.finePreimageFinset,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [computedFactor_eq_coarseRead]

/-- The whole executable preimage table is the finite filter of the raw
factor, an equality convenient for support-table calculations. -/
theorem finePreimage_eq_filter (A : Finset (Fin 2)) :
    presentation.finePreimageFinset A =
      Finset.univ.filter (fun target : Fin 3 => coarseRead target ∈ A) := by
  apply Finset.ext
  intro target
  change Fin 3 at target
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    mem_finePreimage_iff A target

/-- Coarse and fine selected chart tables have the same underlying chart
indices for every coarse target subset. -/
theorem fineChartsIn_eq_coarseChartsIn (A : Finset (Fin 2)) :
    presentation.fineChartsIn A = presentation.coarseChartsIn A := by
  ext chart
  simp only [FiniteComparisonPresentation.fineChartsIn,
    FiniteComparisonPresentation.coarseChartsIn, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [finePreimage_eq_filter]
  fin_cases chart <;>
    simp [Finset.Nonempty, presentation, fineChartSupport,
      coarseChartSupport, coarseRead]

/-- Coarse and fine selected edge tables have the same underlying edge
indices for every coarse target subset. -/
theorem fineEdgesIn_eq_coarseEdgesIn (A : Finset (Fin 2)) :
    presentation.fineEdgesIn A = presentation.coarseEdgesIn A := by
  ext edge
  simp only [FiniteComparisonPresentation.fineEdgesIn,
    FiniteComparisonPresentation.coarseEdgesIn, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [finePreimage_eq_filter]
  fin_cases edge <;>
    simp [Finset.Nonempty,
      FiniteComparisonPresentation.fineEdgeSupportFinset,
      FiniteComparisonPresentation.coarseEdgeSupportFinset, presentation,
      fineChartSupport, coarseChartSupport, edgeLeft, edgeRight, coarseRead]

/-- Coarse and fine selected face tables have the same underlying face
indices for every coarse target subset. -/
theorem fineFacesIn_eq_coarseFacesIn (A : Finset (Fin 2)) :
    presentation.fineFacesIn A = presentation.coarseFacesIn A := by
  ext face
  simp only [FiniteComparisonPresentation.fineFacesIn,
    FiniteComparisonPresentation.coarseFacesIn, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [finePreimage_eq_filter]
  fin_cases face
  simp [Finset.Nonempty,
    FiniteComparisonPresentation.fineFaceSupportFinset,
    FiniteComparisonPresentation.coarseFaceSupportFinset,
    FiniteComparisonPresentation.fineEdgeSupportFinset,
    FiniteComparisonPresentation.coarseEdgeSupportFinset, presentation,
    fineChartSupport, coarseChartSupport, faceEdge0, faceEdge1, faceEdge2,
    edgeLeft, edgeRight, coarseRead]

/-- Forgetting selection proofs identifies every selected fine chart with
the corresponding selected coarse chart. -/
def selectedChartEquiv (A : Finset (Fin 2)) :
    presentation.FineChartIn A ≃ presentation.CoarseChartIn A where
  toFun chart := ⟨chart.1, by
    rw [← fineChartsIn_eq_coarseChartsIn A]
    exact chart.2⟩
  invFun chart := ⟨chart.1, by
    rw [fineChartsIn_eq_coarseChartsIn A]
    exact chart.2⟩
  left_inv chart := Subtype.ext rfl
  right_inv chart := Subtype.ext rfl

/-- Forgetting selection proofs identifies every selected fine edge with
the corresponding selected coarse edge. -/
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

set_option maxHeartbeats 400000 in
/-- Forgetting selection proofs identifies every selected fine face with
the corresponding selected coarse face. -/
def selectedFaceEquiv (A : Finset (Fin 2)) :
    presentation.FineFaceIn A ≃ presentation.CoarseFaceIn A where
  toFun face := ⟨face.1, by
    rw [← fineFacesIn_eq_coarseFacesIn A]
    exact face.2⟩
  invFun face := ⟨face.1, by
    rw [fineFacesIn_eq_coarseFacesIn A]
    exact face.2⟩
  left_inv face := Subtype.ext rfl
  right_inv face := Subtype.ext rfl

/-! ## Degreewise identity reindexing -/

/-- Reindex raw coarse chart cochains onto the corresponding fine charts. -/
def rawChartCochainEquiv (A : Finset (Fin 2)) :
    (presentation.CoarseChartIn A → ℚ) ≃ₗ[ℚ]
      (presentation.FineChartIn A → ℚ) :=
  cochainEquivOfIndexEquiv (selectedChartEquiv A)

/-- Reindex raw coarse edge cochains onto the corresponding fine edges. -/
def rawEdgeCochainEquiv (A : Finset (Fin 2)) :
    (presentation.CoarseEdgeIn A → ℚ) ≃ₗ[ℚ]
      (presentation.FineEdgeIn A → ℚ) :=
  cochainEquivOfIndexEquiv (selectedEdgeEquiv A)

/-- Reindex raw coarse face cochains onto the corresponding fine faces. -/
def rawFaceCochainEquiv (A : Finset (Fin 2)) :
    (presentation.CoarseFaceIn A → ℚ) ≃ₗ[ℚ]
      (presentation.FineFaceIn A → ℚ) :=
  cochainEquivOfIndexEquiv (selectedFaceEquiv A)

/-- Selected edge-left incidence is preserved by the identity cell tables. -/
theorem selectedEquiv_edgeLeft (A : Finset (Fin 2))
    (edge : presentation.FineEdgeIn A) :
    selectedChartEquiv A (presentation.fineEdgeLeftIn A edge) =
      presentation.coarseEdgeLeftIn A (selectedEdgeEquiv A edge) := by
  apply Subtype.ext
  rfl

/-- Selected edge-right incidence is preserved by the identity cell tables. -/
theorem selectedEquiv_edgeRight (A : Finset (Fin 2))
    (edge : presentation.FineEdgeIn A) :
    selectedChartEquiv A (presentation.fineEdgeRightIn A edge) =
      presentation.coarseEdgeRightIn A (selectedEdgeEquiv A edge) := by
  apply Subtype.ext
  rfl

/-- Face-edge zero incidence is preserved by the identity cell tables. -/
theorem selectedEquiv_faceEdge0 (A : Finset (Fin 2))
    (face : presentation.FineFaceIn A) :
    selectedEdgeEquiv A (presentation.fineFaceEdge0In A face) =
      presentation.coarseFaceEdge0In A (selectedFaceEquiv A face) := by
  apply Subtype.ext
  rfl

/-- Face-edge one incidence is preserved by the identity cell tables. -/
theorem selectedEquiv_faceEdge1 (A : Finset (Fin 2))
    (face : presentation.FineFaceIn A) :
    selectedEdgeEquiv A (presentation.fineFaceEdge1In A face) =
      presentation.coarseFaceEdge1In A (selectedFaceEquiv A face) := by
  apply Subtype.ext
  rfl

/-- Face-edge two incidence is preserved by the identity cell tables. -/
theorem selectedEquiv_faceEdge2 (A : Finset (Fin 2))
    (face : presentation.FineFaceIn A) :
    selectedEdgeEquiv A (presentation.fineFaceEdge2In A face) =
      presentation.coarseFaceEdge2In A (selectedFaceEquiv A face) := by
  apply Subtype.ext
  rfl

/-- The raw chart and edge reindexings intertwine degree-zero incidence. -/
theorem rawCochainEquiv_comm0 (A : Finset (Fin 2))
    (cochain : presentation.CoarseChartIn A → ℚ) :
    rawEdgeCochainEquiv A (presentation.coarseD0LinearMap A cochain) =
      presentation.fineD0LinearMap A (rawChartCochainEquiv A cochain) := by
  funext edge
  change
    cochain (presentation.coarseEdgeRightIn A (selectedEdgeEquiv A edge)) -
        cochain (presentation.coarseEdgeLeftIn A (selectedEdgeEquiv A edge)) =
      cochain (selectedChartEquiv A (presentation.fineEdgeRightIn A edge)) -
        cochain (selectedChartEquiv A (presentation.fineEdgeLeftIn A edge))
  rw [selectedEquiv_edgeRight, selectedEquiv_edgeLeft]

/-- The raw edge and face reindexings intertwine degree-one incidence. -/
theorem rawCochainEquiv_comm1 (A : Finset (Fin 2))
    (cochain : presentation.CoarseEdgeIn A → ℚ) :
    rawFaceCochainEquiv A (presentation.coarseD1LinearMap A cochain) =
      presentation.fineD1LinearMap A (rawEdgeCochainEquiv A cochain) := by
  funext face
  change
    cochain (presentation.coarseFaceEdge0In A (selectedFaceEquiv A face)) -
          cochain (presentation.coarseFaceEdge1In A
            (selectedFaceEquiv A face)) +
        cochain (presentation.coarseFaceEdge2In A
          (selectedFaceEquiv A face)) =
      cochain (selectedEdgeEquiv A (presentation.fineFaceEdge0In A face)) -
          cochain (selectedEdgeEquiv A (presentation.fineFaceEdge1In A face)) +
        cochain (selectedEdgeEquiv A (presentation.fineFaceEdge2In A face))
  rw [selectedEquiv_faceEdge0, selectedEquiv_faceEdge1,
    selectedEquiv_faceEdge2]

/-- The restricted raw edge map is the selected-edge equivalence, derived
from the original total identity edge table. -/
theorem edgeMapOptionIn_eq_some_selected (A : Finset (Fin 2))
    (edge : presentation.FineEdgeIn A) :
    presentation.edgeMapOptionIn A edge = some (selectedEdgeEquiv A edge) := by
  simp [FiniteComparisonPresentation.edgeMapOptionIn, presentation,
    selectedEdgeEquiv]

/-- Raw degree-one comparison pullback is exactly edge reindexing. -/
theorem edgePullback1_eq_rawEdgeCochainEquiv (A : Finset (Fin 2))
    (cochain : presentation.CoarseEdgeIn A → ℚ) :
    presentation.edgePullback1LinearMap A cochain =
      rawEdgeCochainEquiv A cochain := by
  funext edge
  change (presentation.edgeMapOptionIn A edge).elim 0 cochain =
    cochain (selectedEdgeEquiv A edge)
  rw [edgeMapOptionIn_eq_some_selected]
  rfl

/-! ## Actual selected-complex equivalence -/

/-- Degree-zero equivalence from the actual coarse A-subnerve to the actual
fine canonical-preimage subnerve. -/
noncomputable def semanticChartCochainEquiv (A : Finset (Fin 2)) :
    (presentation.coarseSupportedNerve.targetSubsetComplex
        (↑A : Set (Fin 2))).C0 ≃ₗ[ℚ]
      (presentation.fineSupportedNerve.targetSubsetComplex
        (presentation.canonicalFinePreimage A)).C0 :=
  (presentation.coarseChartCochainEquiv A).trans
    ((rawChartCochainEquiv A).trans
      (presentation.fineChartCochainEquiv A).symm)

/-- Degree-one equivalence from the actual coarse A-subnerve to the actual
fine canonical-preimage subnerve. -/
noncomputable def semanticEdgeCochainEquiv (A : Finset (Fin 2)) :
    (presentation.coarseSupportedNerve.targetSubsetComplex
        (↑A : Set (Fin 2))).C1 ≃ₗ[ℚ]
      (presentation.fineSupportedNerve.targetSubsetComplex
        (presentation.canonicalFinePreimage A)).C1 :=
  (presentation.coarseEdgeCochainEquiv A).trans
    ((rawEdgeCochainEquiv A).trans
      (presentation.fineEdgeCochainEquiv A).symm)

/-- Degree-two equivalence from the actual coarse A-subnerve to the actual
fine canonical-preimage subnerve. -/
noncomputable def semanticFaceCochainEquiv (A : Finset (Fin 2)) :
    (presentation.coarseSupportedNerve.targetSubsetComplex
        (↑A : Set (Fin 2))).C2 ≃ₗ[ℚ]
      (presentation.fineSupportedNerve.targetSubsetComplex
        (presentation.canonicalFinePreimage A)).C2 :=
  (presentation.coarseFaceCochainEquiv A).trans
    ((rawFaceCochainEquiv A).trans
      (presentation.fineFaceCochainEquiv A).symm)

/-- The actual degree-zero differentials commute with the generated
degreewise equivalences. -/
theorem semanticCochainEquiv_comm0 (A : Finset (Fin 2))
    (cochain : (presentation.coarseSupportedNerve.targetSubsetComplex
      (↑A : Set (Fin 2))).C0) :
    semanticEdgeCochainEquiv A
        ((presentation.coarseSupportedNerve.targetSubsetComplex
          (↑A : Set (Fin 2))).d0 cochain) =
      (presentation.fineSupportedNerve.targetSubsetComplex
        (presentation.canonicalFinePreimage A)).d0
        (semanticChartCochainEquiv A cochain) := by
  apply (presentation.fineEdgeCochainEquiv A).injective
  have hcoarse :
      presentation.coarseD0LinearMap A
          (presentation.coarseChartCochainEquiv A cochain) =
        presentation.coarseEdgeCochainEquiv A
          ((presentation.coarseSupportedNerve.targetSubsetComplex
            (↑A : Set (Fin 2))).d0 cochain) :=
    presentation.coarseD0_commutes A cochain
  have hfine :
      presentation.fineD0LinearMap A
          (presentation.fineChartCochainEquiv A
            (semanticChartCochainEquiv A cochain)) =
        presentation.fineEdgeCochainEquiv A
          ((presentation.fineSupportedNerve.targetSubsetComplex
            (presentation.canonicalFinePreimage A)).d0
              (semanticChartCochainEquiv A cochain)) :=
    presentation.fineD0_commutes A (semanticChartCochainEquiv A cochain)
  calc
    presentation.fineEdgeCochainEquiv A
        (semanticEdgeCochainEquiv A
          ((presentation.coarseSupportedNerve.targetSubsetComplex
            (↑A : Set (Fin 2))).d0 cochain)) =
      rawEdgeCochainEquiv A
        (presentation.coarseEdgeCochainEquiv A
          ((presentation.coarseSupportedNerve.targetSubsetComplex
            (↑A : Set (Fin 2))).d0 cochain)) := by
        change presentation.fineEdgeCochainEquiv A
            ((presentation.fineEdgeCochainEquiv A).symm
              (rawEdgeCochainEquiv A
                (presentation.coarseEdgeCochainEquiv A
                  ((presentation.coarseSupportedNerve.targetSubsetComplex
                    (↑A : Set (Fin 2))).d0 cochain)))) = _
        exact (presentation.fineEdgeCochainEquiv A).apply_symm_apply _
    _ = rawEdgeCochainEquiv A
        (presentation.coarseD0LinearMap A
          (presentation.coarseChartCochainEquiv A cochain)) := by
        rw [hcoarse]
    _ = presentation.fineD0LinearMap A
        (rawChartCochainEquiv A
          (presentation.coarseChartCochainEquiv A cochain)) :=
      rawCochainEquiv_comm0 A
        (presentation.coarseChartCochainEquiv A cochain)
    _ = presentation.fineD0LinearMap A
        (presentation.fineChartCochainEquiv A
          (semanticChartCochainEquiv A cochain)) := by
        congr 1
    _ = presentation.fineEdgeCochainEquiv A
        ((presentation.fineSupportedNerve.targetSubsetComplex
          (presentation.canonicalFinePreimage A)).d0
            (semanticChartCochainEquiv A cochain)) := hfine

/-- The actual degree-one differentials commute with the generated
degreewise equivalences. -/
theorem semanticCochainEquiv_comm1 (A : Finset (Fin 2))
    (cochain : (presentation.coarseSupportedNerve.targetSubsetComplex
      (↑A : Set (Fin 2))).C1) :
    semanticFaceCochainEquiv A
        ((presentation.coarseSupportedNerve.targetSubsetComplex
          (↑A : Set (Fin 2))).d1 cochain) =
      (presentation.fineSupportedNerve.targetSubsetComplex
        (presentation.canonicalFinePreimage A)).d1
        (semanticEdgeCochainEquiv A cochain) := by
  apply (presentation.fineFaceCochainEquiv A).injective
  have hcoarse :
      presentation.coarseD1LinearMap A
          (presentation.coarseEdgeCochainEquiv A cochain) =
        presentation.coarseFaceCochainEquiv A
          ((presentation.coarseSupportedNerve.targetSubsetComplex
            (↑A : Set (Fin 2))).d1 cochain) :=
    presentation.coarseD1_commutes A cochain
  have hfine :
      presentation.fineD1LinearMap A
          (presentation.fineEdgeCochainEquiv A
            (semanticEdgeCochainEquiv A cochain)) =
        presentation.fineFaceCochainEquiv A
          ((presentation.fineSupportedNerve.targetSubsetComplex
            (presentation.canonicalFinePreimage A)).d1
              (semanticEdgeCochainEquiv A cochain)) :=
    presentation.fineD1_commutes A (semanticEdgeCochainEquiv A cochain)
  calc
    presentation.fineFaceCochainEquiv A
        (semanticFaceCochainEquiv A
          ((presentation.coarseSupportedNerve.targetSubsetComplex
            (↑A : Set (Fin 2))).d1 cochain)) =
      rawFaceCochainEquiv A
        (presentation.coarseFaceCochainEquiv A
          ((presentation.coarseSupportedNerve.targetSubsetComplex
            (↑A : Set (Fin 2))).d1 cochain)) := by
        change presentation.fineFaceCochainEquiv A
            ((presentation.fineFaceCochainEquiv A).symm
              (rawFaceCochainEquiv A
                (presentation.coarseFaceCochainEquiv A
                  ((presentation.coarseSupportedNerve.targetSubsetComplex
                    (↑A : Set (Fin 2))).d1 cochain)))) = _
        exact (presentation.fineFaceCochainEquiv A).apply_symm_apply _
    _ = rawFaceCochainEquiv A
        (presentation.coarseD1LinearMap A
          (presentation.coarseEdgeCochainEquiv A cochain)) := by
        rw [hcoarse]
    _ = presentation.fineD1LinearMap A
        (rawEdgeCochainEquiv A
          (presentation.coarseEdgeCochainEquiv A cochain)) :=
      rawCochainEquiv_comm1 A
        (presentation.coarseEdgeCochainEquiv A cochain)
    _ = presentation.fineD1LinearMap A
        (presentation.fineEdgeCochainEquiv A
          (semanticEdgeCochainEquiv A cochain)) := by
        congr 1
    _ = presentation.fineFaceCochainEquiv A
        ((presentation.fineSupportedNerve.targetSubsetComplex
          (presentation.canonicalFinePreimage A)).d1
            (semanticEdgeCochainEquiv A cochain)) := hfine

/-- The raw support correspondence generates an actual cochain equivalence
for every finite coarse target subset. -/
noncomputable def semanticCochainEquiv (A : Finset (Fin 2)) :
    ThreeCochainComplex.CochainEquiv
      (presentation.coarseSupportedNerve.targetSubsetComplex
        (↑A : Set (Fin 2)))
      (presentation.fineSupportedNerve.targetSubsetComplex
        (presentation.canonicalFinePreimage A)) where
  e0 := semanticChartCochainEquiv A
  e1 := semanticEdgeCochainEquiv A
  e2 := semanticFaceCochainEquiv A
  comm0 := semanticCochainEquiv_comm0 A
  comm1 := semanticCochainEquiv_comm1 A

/-- The actual canonical comparison's degree-one map is the degree-one map
of the generated cochain equivalence. -/
theorem aSubnerveComparisonHom_f1_eq_semanticEquiv
    (A : Finset (Fin 2))
    (cochain : (presentation.coarseSupportedNerve.targetSubsetComplex
      (↑A : Set (Fin 2))).C1) :
    (presentation.toGeometry.aSubnerveComparisonHom
        (↑A : Set (Fin 2))).f1 cochain =
      semanticEdgeCochainEquiv A cochain := by
  apply (presentation.fineEdgeCochainEquiv A).injective
  rw [← presentation.edgePullback1_commutes A cochain]
  simp only [semanticEdgeCochainEquiv, LinearEquiv.trans_apply]
  exact edgePullback1_eq_rawEdgeCochainEquiv A
    (presentation.coarseEdgeCochainEquiv A cochain)

/-- On every finite target subset, the actual canonical H1 map agrees with
the H1 map induced by the generated cochain equivalence. -/
theorem aSubnerveComparisonHom_h1Map_eq_semanticEquiv
    (A : Finset (Fin 2))
    (cohomologyClass : (presentation.coarseSupportedNerve.targetSubsetComplex
      (↑A : Set (Fin 2))).H1) :
    (presentation.toGeometry.aSubnerveComparisonHom
        (↑A : Set (Fin 2))).h1Map cohomologyClass =
      (semanticCochainEquiv A).toHom.h1Map cohomologyClass := by
  obtain ⟨cycle, rfl⟩ :=
    (LinearMap.range
      (presentation.coarseSupportedNerve.targetSubsetComplex
        (↑A : Set (Fin 2))).boundaryToCycles).mkQ_surjective cohomologyClass
  rw [ThreeCochainComplex.Hom.h1Map_mk,
    ThreeCochainComplex.Hom.h1Map_mk]
  apply congrArg
    (LinearMap.range
      (presentation.fineSupportedNerve.targetSubsetComplex
        (presentation.canonicalFinePreimage A)).boundaryToCycles).mkQ
  apply Subtype.ext
  exact aSubnerveComparisonHom_f1_eq_semanticEquiv A cycle.1

/-- Every actual canonical H1 comparison of the R1 presentation is
bijective, including the empty subset. -/
theorem aSubnerveComparisonHom_h1Map_bijective (A : Finset (Fin 2)) :
    Function.Bijective
      (presentation.toGeometry.aSubnerveComparisonHom
        (↑A : Set (Fin 2))).h1Map := by
  have hmaps :
      (presentation.toGeometry.aSubnerveComparisonHom
          (↑A : Set (Fin 2))).h1Map =
        (semanticCochainEquiv A).toHom.h1Map := by
    apply LinearMap.ext
    intro cohomologyClass
    exact aSubnerveComparisonHom_h1Map_eq_semanticEquiv A cohomologyClass
  rw [hmaps]
  exact (semanticCochainEquiv A).toHom_h1Map_bijective

/-! ## Exact checker firing and semantic uniformity -/

/-- Every finite target subset has zero literal and executable H1 defect. -/
theorem all_computedASubnerveDefects_zero (A : Finset (Fin 2)) :
    presentation.computedASubnerveDefect A = (0, 0) := by
  rw [presentation.computedASubnerveDefect_eq_aSubnerveDefect]
  exact
    (presentation.toGeometry.aSubnerveDefect_eq_zero_iff_bijective
      (↑A : Set (Fin 2))).2
      (aSubnerveComparisonHom_h1Map_bijective A)

/-- The generic all-subset uniformity checker accepts the raw R1 table. -/
theorem uniformPresentationCheck_true :
    presentation.uniformPresentationCheck = true := by
  apply
    (presentation.uniformPresentationCheck_eq_true_iff_allNonemptyDefects).2
  intro A _hA
  exact all_computedASubnerveDefects_zero A

/-- The exact R1 presentation is uniformly invariant for every finite law
family adequate for both readings. -/
theorem uniformPresentation : UniformPresentation presentation :=
  presentation.uniformPresentationCheck_eq_true_iff.mp
    uniformPresentationCheck_true

/-! ## Direct C3 failure on target zero -/

/-- The unique coarse chart selected by target zero. -/
def coarseChartZero : presentation.CoarseChartIn targetZero :=
  ⟨(0 : Fin 3), by decide⟩

/-- The unique fine self-loop selected over target zero. -/
def fineEdgeZero : presentation.FineEdgeIn targetZero :=
  ⟨(0 : Fin 3), by decide⟩

/-- Constant coefficient one on the selected fine self-loop. -/
def loopChain : presentation.FineEdgeIn targetZero → ℚ :=
  fun _ => 1

/-- Every fine chart selected over target zero is chart zero. -/
theorem fineChartAtTargetZero_eq_zero
    (chart : presentation.FineChartIn targetZero) : chart.1 = (0 : Fin 3) := by
  rcases chart with ⟨chart, hmem⟩
  simp only [FiniteComparisonPresentation.fineChartsIn,
    Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  rw [finePreimage_targetZero] at hmem
  fin_cases chart <;> simp [presentation, fineChartSupport] at hmem ⊢

/-- Every fine edge selected over target zero is edge zero. -/
theorem fineEdgeAtTargetZero_eq_zero
    (edge : presentation.FineEdgeIn targetZero) : edge.1 = (0 : Fin 3) := by
  rcases edge with ⟨edge, hmem⟩
  simp only [FiniteComparisonPresentation.fineEdgesIn,
    Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  rw [finePreimage_targetZero] at hmem
  fin_cases edge <;>
    simp [FiniteComparisonPresentation.fineEdgeSupportFinset,
      presentation, fineChartSupport, edgeLeft, edgeRight] at hmem ⊢

/-- The selected self-loop satisfies the raw fiber-cycle constraint. -/
theorem loopChain_constraint :
    presentation.fiberCycleConstraintLinearMap targetZero coarseChartZero
      loopChain = 0 := by
  funext row
  simp only [Pi.zero_apply]
  cases row with
  | inl edge =>
      rw [presentation.fiberCycleConstraintLinearMap_apply_inl]
      have hfiber : presentation.rawFiberEdge targetZero coarseChartZero edge := by
        have hedge := fineEdgeAtTargetZero_eq_zero edge
        constructor
        · apply Subtype.ext
          change edgeLeft edge.1 = (0 : Fin 3)
          rw [hedge]
          rfl
        · apply Subtype.ext
          change edgeRight edge.1 = (0 : Fin 3)
          rw [hedge]
          rfl
      simp [hfiber]
  | inr chart =>
      rw [presentation.fiberCycleConstraintLinearMap_apply_inr]
      have hmap : presentation.chartMapIn targetZero chart = coarseChartZero := by
        apply Subtype.ext
        change chart.1 = (0 : Fin 3)
        exact fineChartAtTargetZero_eq_zero chart
      rw [if_pos hmap, sub_eq_zero]
      rw [presentation.rawFiberIncoming_apply,
        presentation.rawFiberOutgoing_apply]
      apply Finset.sum_congr rfl
      intro edge _hedge
      have hendpoints : presentation.fineEdgeRightIn targetZero edge =
          presentation.fineEdgeLeftIn targetZero edge := by
        apply Subtype.ext
        have hedge := fineEdgeAtTargetZero_eq_zero edge
        change edgeRight edge.1 = edgeLeft edge.1
        rw [hedge]
        rfl
      rw [hendpoints]

/-- No fine face is selected by target zero. -/
theorem noFineFaceAtTargetZero
    (face : presentation.FineFaceIn targetZero) : False := by
  rcases face with ⟨face, hmem⟩
  simp only [FiniteComparisonPresentation.fineFacesIn,
    Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  rw [finePreimage_targetZero] at hmem
  fin_cases face
  simp [FiniteComparisonPresentation.fineFaceSupportFinset,
      FiniteComparisonPresentation.fineEdgeSupportFinset,
      presentation, fineChartSupport, faceEdge0, faceEdge1, faceEdge2,
      edgeLeft, edgeRight] at hmem

/-! ## Nonzero H1 on the same target-zero block -/

/-- The actual coarse constant-rational complex on target zero. -/
abbrev coarseTargetZeroComplex : ThreeCochainComplex ℚ :=
  presentation.coarseSupportedNerve.targetSubsetComplex
    (↑targetZero : Set (Fin 2))

/-- The actual fine constant-rational complex on the canonical preimage of
target zero. -/
abbrev fineTargetZeroComplex : ThreeCochainComplex ℚ :=
  presentation.fineSupportedNerve.targetSubsetComplex
    (presentation.canonicalFinePreimage targetZero)

/-- The unique selected raw coarse self-loop at target zero. -/
def coarseEdgeZero : presentation.CoarseEdgeIn targetZero :=
  ⟨(0 : Fin 3), by decide⟩

/-- The corresponding actual selected coarse self-loop. -/
def coarseActualEdgeZero :
    presentation.coarseSupportedNerve.EdgeInTargetSubset
      (↑targetZero : Set (Fin 2)) :=
  presentation.coarseEdgeEquiv targetZero coarseEdgeZero

/-- No coarse face is selected by target zero. -/
theorem noCoarseFaceAtTargetZero
    (face : presentation.CoarseFaceIn targetZero) : False := by
  exact noFineFaceAtTargetZero
    ((selectedFaceEquiv targetZero).symm face)

/-- Evaluation on the isolated target-zero self-loop. -/
def coarseTargetZeroPeriod (cochain : coarseTargetZeroComplex.C1) : ℚ :=
  cochain coarseActualEdgeZero

/-- Every actual coarse coboundary has zero target-zero loop period. -/
theorem coarseTargetZeroPeriod_boundary_zero
    (cochain : coarseTargetZeroComplex.C0) :
    coarseTargetZeroPeriod (coarseTargetZeroComplex.d0 cochain) = 0 := by
  change cochain
      (presentation.coarseSupportedNerve.targetSubsetEdgeRight
        (↑targetZero : Set (Fin 2)) coarseActualEdgeZero) -
      cochain
        (presentation.coarseSupportedNerve.targetSubsetEdgeLeft
          (↑targetZero : Set (Fin 2)) coarseActualEdgeZero) = 0
  have hloop :
      presentation.coarseSupportedNerve.targetSubsetEdgeRight
          (↑targetZero : Set (Fin 2)) coarseActualEdgeZero =
        presentation.coarseSupportedNerve.targetSubsetEdgeLeft
          (↑targetZero : Set (Fin 2)) coarseActualEdgeZero := by
    apply Subtype.ext
    rfl
  rw [hloop]
  ring

/-- Constant coefficient one on the actual coarse target-zero self-loop. -/
def coarseTargetZeroCochain : coarseTargetZeroComplex.C1 :=
  fun _ => 1

/-- The target-zero self-loop cochain is an actual cocycle. -/
theorem coarseTargetZeroCochain_cocycle :
    coarseTargetZeroComplex.d1 coarseTargetZeroCochain = 0 := by
  funext face
  exact (noCoarseFaceAtTargetZero
    ((presentation.coarseFaceEquiv targetZero).symm face)).elim

/-- The target-zero cocycle as an element of the actual kernel. -/
def coarseTargetZeroCycle : LinearMap.ker coarseTargetZeroComplex.d1 :=
  ⟨coarseTargetZeroCochain, coarseTargetZeroCochain_cocycle⟩

/-- The actual quotient-H1 class of the isolated self-loop. -/
def coarseTargetZeroClass : coarseTargetZeroComplex.H1 :=
  (LinearMap.range coarseTargetZeroComplex.boundaryToCycles).mkQ
    coarseTargetZeroCycle

/-- The displayed target-zero cocycle has unit period. -/
theorem coarseTargetZeroPeriod_cycle :
    coarseTargetZeroPeriod coarseTargetZeroCycle.1 = 1 := by
  rfl

/-- The actual coarse target-zero quotient class is nonzero. -/
theorem coarseTargetZeroClass_ne_zero : coarseTargetZeroClass ≠ 0 := by
  intro hzero
  have hmem := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range coarseTargetZeroComplex.boundaryToCycles)).1 hzero
  rcases hmem with ⟨cochain, hcochain⟩
  have hperiod := congrArg
    (fun cycle : LinearMap.ker coarseTargetZeroComplex.d1 =>
      coarseTargetZeroPeriod cycle.1) hcochain
  change coarseTargetZeroPeriod (coarseTargetZeroComplex.d0 cochain) =
    coarseTargetZeroPeriod coarseTargetZeroCycle.1 at hperiod
  rw [coarseTargetZeroPeriod_boundary_zero,
    coarseTargetZeroPeriod_cycle] at hperiod
  exact zero_ne_one hperiod

/-- The coarse target-zero H1 space has positive finite dimension. -/
theorem targetZero_coarse_h1_pos :
    0 < Module.finrank ℚ coarseTargetZeroComplex.H1 :=
  Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨coarseTargetZeroClass, coarseTargetZeroClass_ne_zero⟩

/-- The actual fine class obtained from the canonical target-zero comparison. -/
def fineTargetZeroClass : fineTargetZeroComplex.H1 :=
  (presentation.toGeometry.aSubnerveComparisonHom
    (↑targetZero : Set (Fin 2))).h1Map coarseTargetZeroClass

/-- The fine canonical image is nonzero by actual comparison injectivity. -/
theorem fineTargetZeroClass_ne_zero : fineTargetZeroClass ≠ 0 := by
  intro hzero
  apply coarseTargetZeroClass_ne_zero
  apply (aSubnerveComparisonHom_h1Map_bijective targetZero).1
  simpa only [fineTargetZeroClass, map_zero] using hzero

/-- The fine canonical-preimage H1 space has positive finite dimension. -/
theorem targetZero_fine_h1_pos :
    0 < Module.finrank ℚ fineTargetZeroComplex.H1 :=
  Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨fineTargetZeroClass, fineTargetZeroClass_ne_zero⟩

/-- Both sides of the same C3-failing target-zero comparison have nonzero H1. -/
theorem targetZero_both_h1_pos :
    0 < Module.finrank ℚ coarseTargetZeroComplex.H1 ∧
      0 < Module.finrank ℚ fineTargetZeroComplex.H1 :=
  ⟨targetZero_coarse_h1_pos, targetZero_fine_h1_pos⟩

/-- The target-zero loop is not in the image of the internal-face boundary. -/
theorem loopChain_not_internalFaceImage :
    ¬ ∃ faces : presentation.FineFaceIn targetZero → ℚ,
      presentation.internalFaceBoundaryLinearMap targetZero coarseChartZero
        faces = loopChain := by
  rintro ⟨faces, hboundary⟩
  have heq := congrFun hboundary fineEdgeZero
  rw [presentation.internalFaceBoundaryLinearMap_apply] at heq
  have hzeroSum
      (summand : presentation.FineFaceIn targetZero → ℚ) :
      ∑ face, summand face = 0 := by
    apply Finset.sum_eq_zero
    intro face _hface
    exact (noFineFaceAtTargetZero face).elim
  simp only [hzeroSum, zero_sub, loopChain] at heq
  norm_num at heq

/-- Raw C3 fails at target zero. -/
theorem not_rawConditionC3At :
    ¬ presentation.RawConditionC3At targetZero := by
  intro hraw
  exact loopChain_not_internalFaceImage
    (hraw coarseChartZero loopChain loopChain_constraint)

/-- The executable C3 checker rejects target zero. -/
theorem conditionC3AtTargetSubsetCheck_false :
    presentation.conditionC3AtTargetSubsetCheck targetZero = false := by
  cases hcheck : presentation.conditionC3AtTargetSubsetCheck targetZero
  · rfl
  · exfalso
    exact not_rawConditionC3At
      ((presentation.conditionC3AtTargetSubsetCheck_eq_true_iff_raw
        targetZero).1 hcheck)

/-- Semantic C3 fails on the actual canonical target-zero A-subnerve. -/
theorem not_conditionC3AtTargetSubset :
    ¬ presentation.toGeometry.ConditionC3AtTargetSubset
      (↑targetZero : Set (Fin 2)) := by
  intro hsemantic
  exact not_rawConditionC3At
    ((presentation.rawConditionC3At_iff_conditionC3AtTargetSubset
      targetZero).2 hsemantic)

/-- Hence the geometric all-subset Condition C predicate fails directly at
its target-zero C3 projection. -/
theorem not_conditionCAllA : ¬ presentation.toGeometry.ConditionCAllA := by
  intro hAllA
  exact not_conditionC3AtTargetSubset
    (TargetSupportedNerveMorphism.ConditionCAllA.conditionC3At
      presentation.toGeometry hAllA (↑targetZero : Set (Fin 2))
      targetZero_nonempty)

/-- The generic all-clause checker rejects the same raw presentation. -/
theorem conditionCAllACheck_false :
    presentation.conditionCAllACheck = false := by
  cases hcheck : presentation.conditionCAllACheck
  · rfl
  · exfalso
    exact not_conditionCAllA
      ((presentation.conditionCAllACheck_eq_true_iff).1 hcheck)

/-! ## The same failure under a nonconstant indicator law -/

/-- The target-zero Boolean indicator family on the coarse reading. -/
noncomputable def indicatorLaws : FiniteLawFamily presentation.Source :=
  indicatorLawFamily presentation.coarseReading
    (↑targetZero : Set (Fin 2))

/-- Canonical adequacy of the target-zero indicator on the coarse reading. -/
theorem indicatorCoarseAdequate :
    indicatorLaws.Adequate presentation.coarseReading :=
  indicatorLawFamily_adequate presentation.coarseReading
    (↑targetZero : Set (Fin 2))

/-- Canonical adequacy of the same indicator on the fine reading. -/
theorem indicatorFineAdequate :
    indicatorLaws.Adequate presentation.fineReading :=
  indicatorLawFamily_adequate_of_coarserThan presentation.coarseReading
    presentation.fineReading presentation.coarserThan
    (↑targetZero : Set (Fin 2))

/-- The source-generated true label of the target-zero indicator. -/
noncomputable def indicatorLabel : LawValueLabel indicatorLaws :=
  indicatorLawFamilyTrueLabel presentation.coarseReading
    (↑targetZero : Set (Fin 2)) targetZero_nonempty

/-- The indicator law genuinely distinguishes sources zero and two. -/
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

/-- Law-indexed C3 fails at the source-generated true indicator label. -/
theorem indicator_not_conditionC3At :
    ¬ presentation.toGeometry.ConditionC3At indicatorLaws
      indicatorCoarseAdequate indicatorFineAdequate indicatorLabel := by
  intro hC3
  have hsubset :=
    presentation.toGeometry.conditionC3AtTargetSubset_of_conditionC3At_labelValueFiber
        indicatorLaws indicatorCoarseAdequate indicatorFineAdequate
        indicatorLabel hC3
  have hfiber :
      labelValueFiber indicatorLaws presentation.coarseReading
          indicatorCoarseAdequate indicatorLabel =
        (↑targetZero : Set (Fin 2)) := by
    exact indicatorLawFamily_trueFiber_eq presentation.coarseReading
      (↑targetZero : Set (Fin 2)) targetZero_nonempty
  rw [hfiber] at hsubset
  exact not_conditionC3AtTargetSubset hsubset

/-- The full law-indexed C3 clause fails for the nonconstant indicator family. -/
theorem indicator_not_conditionC3 :
    ¬ presentation.toGeometry.ConditionC3 indicatorLaws
      indicatorCoarseAdequate indicatorFineAdequate := by
  intro hC3
  exact indicator_not_conditionC3At (hC3 indicatorLabel)

/-! ## Bounded R1 necessity conclusion -/

/-- Exact C3 non-necessity witness: one raw presentation is uniformly
invariant, fails both the law-free and nonconstant-law C3 clauses at the same
target-zero block, and has nonzero H1 on both sides of that block. -/
theorem c3_not_necessary :
    UniformPresentation presentation ∧
      ¬ presentation.toGeometry.ConditionC3 indicatorLaws
        indicatorCoarseAdequate indicatorFineAdequate ∧
      ¬ presentation.toGeometry.ConditionC3AtTargetSubset
        (↑targetZero : Set (Fin 2)) ∧
      ¬ presentation.toGeometry.ConditionCAllA ∧
      0 < Module.finrank ℚ coarseTargetZeroComplex.H1 ∧
      0 < Module.finrank ℚ fineTargetZeroComplex.H1 :=
  ⟨uniformPresentation, indicator_not_conditionC3,
    not_conditionC3AtTargetSubset, not_conditionCAllA,
    targetZero_coarse_h1_pos, targetZero_fine_h1_pos⟩

end R1ConditionC3Witness

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
