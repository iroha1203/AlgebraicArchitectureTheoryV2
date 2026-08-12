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

/-- The proper coarse reading table `[0, 0, 1]`.  This is canonical R1 raw
fixture data used to construct `presentation`, not a theorem premise. -/
def coarseRead (source : Fin 3) : Fin 2 :=
  if source = 2 then 1 else 0

/-- Left endpoints of the three edges `(0,0)`, `(1,2)`, and `(2,2)`.  This
canonical R1 raw-incidence datum feeds `presentation` and carries no result
certificate. -/
def edgeLeft (edge : Fin 3) : Fin 3 :=
  if edge = 1 then 1 else if edge = 2 then 2 else 0

/-- Right endpoints of the three edges `(0,0)`, `(1,2)`, and `(2,2)`.  This
canonical R1 raw-incidence datum feeds `presentation` and carries no result
certificate. -/
def edgeRight (edge : Fin 3) : Fin 3 :=
  if edge = 1 then 2 else if edge = 2 then 2 else 0

/-- The first edge of the unique face boundary `(1,1,2)`.  This is raw R1
face-incidence input to `presentation`, before any C3 conclusion is proved. -/
def faceEdge0 (_face : Fin 1) : Fin 3 := 1

/-- The second edge of the unique face boundary `(1,1,2)`.  This is raw R1
face-incidence input to `presentation`, before any C3 conclusion is proved. -/
def faceEdge1 (_face : Fin 1) : Fin 3 := 1

/-- The third edge of the unique face boundary `(1,1,2)`.  This is raw R1
face-incidence input to `presentation`, before any C3 conclusion is proved. -/
def faceEdge2 (_face : Fin 1) : Fin 3 := 2

/-- Coarse supports `{0}`, `{1}`, `{1}` on charts zero, one, and two.  This
canonical R1 support table is raw presentation data, not supplied uniformity
or cohomology evidence. -/
def coarseChartSupport (chart : Fin 3) : Finset (Fin 2) :=
  if chart = 0 then {0} else {1}

/-- Fine supports `{0,1}`, `{2}`, `{2}` on charts zero, one, and two.  This
canonical R1 support table is raw presentation data, not supplied uniformity
or cohomology evidence. -/
def fineChartSupport (chart : Fin 3) : Finset (Fin 3) :=
  if chart = 0 then {0, 1} else {2}

/-- The exact finite raw presentation underlying the R1 C3 witness.  This is
the Cycle 15 fixture constructor feeding the main theorem: its fields come
only from canonical raw readings, incidence, support, partial maps, and their
well-formedness proofs, never from a factor, rank, H¹, C3, or truth result. -/
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
`[0,0,1]`; no factor is stored in the presentation.  This Cycle 15 API lemma
connects executable factor search to the raw fixture table and discharges the
factor provenance needed by subsequent selected-cell proofs. -/
theorem computedFactor_eq_coarseRead :
    presentation.computedFactor = coarseRead := by
  funext target
  fin_cases target <;>
    decide

/-- The canonical semantic comparison factor is the same proper factor
`[0,0,1]`, by uniqueness from the raw reading tables.  This is the semantic
factor API used by the witness route; its only premise is the already
constructed raw presentation and canonical uniqueness. -/
theorem comparisonFactor_eq_coarseRead :
    comparisonFactor presentation.coarseReading presentation.fineReading
      presentation.coarserThan = coarseRead := by
  rw [← presentation.computedFactor_eq_comparisonFactor]
  exact computedFactor_eq_coarseRead

/-- The singleton coarse target on which the unfilled self-loop is selected.
This Cycle 15 fixture datum names the common C3-failure/nonzero-H¹ block; it is
not chosen from a supplied failure certificate. -/
def targetZero : Finset (Fin 2) := {0}

/-- Target zero is a nonempty semantic subset.  This API lemma discharges the
nonemptiness premise for `ConditionCAllA` projection and indicator-fiber
transport directly from the explicit singleton datum. -/
theorem targetZero_nonempty :
    (↑targetZero : Set (Fin 2)).Nonempty := by
  exact ⟨0, by simp [targetZero]⟩

/-- Coarse and fine selected chart tables have the same underlying chart
indices for every coarse target subset.  This all-subset transport API is
derived from raw support tables and `computedFactor_eq_coarseRead`; it supplies
no selected equivalence or uniformity certificate. -/
theorem fineChartsIn_eq_coarseChartsIn (A : Finset (Fin 2)) :
    presentation.fineChartsIn A = presentation.coarseChartsIn A := by
  ext chart
  rw [presentation.mem_fineChartsIn_iff_raw,
    presentation.mem_coarseChartsIn_iff_raw,
    computedFactor_eq_coarseRead]
  fin_cases chart <;>
    simp [presentation, fineChartSupport,
      coarseChartSupport, coarseRead]

/-- Coarse and fine selected edge tables have the same underlying edge
indices for every coarse target subset.  This all-subset transport API is
derived from raw endpoint support and the computed factor, and supports the
degree-one comparison in the main witness route. -/
theorem fineEdgesIn_eq_coarseEdgesIn (A : Finset (Fin 2)) :
    presentation.fineEdgesIn A = presentation.coarseEdgesIn A := by
  ext edge
  rw [presentation.mem_fineEdgesIn_iff_raw,
    presentation.mem_coarseEdgesIn_iff_raw,
    computedFactor_eq_coarseRead]
  simp only [presentation.mem_fineEdgeSupportFinset_iff_raw,
    presentation.mem_coarseEdgeSupportFinset_iff_raw]
  fin_cases edge <;>
    simp [presentation,
      fineChartSupport, coarseChartSupport, edgeLeft, edgeRight, coarseRead]

/-- Coarse and fine selected face tables have the same underlying face
indices for every coarse target subset.  This all-subset transport API is
derived from raw boundary-edge support and the computed factor, before any H¹
or C3 conclusion is used. -/
theorem fineFacesIn_eq_coarseFacesIn (A : Finset (Fin 2)) :
    presentation.fineFacesIn A = presentation.coarseFacesIn A := by
  ext face
  rw [presentation.mem_fineFacesIn_iff_raw,
    presentation.mem_coarseFacesIn_iff_raw,
    computedFactor_eq_coarseRead]
  simp only [presentation.mem_fineFaceSupportFinset_iff_raw,
    presentation.mem_coarseFaceSupportFinset_iff_raw,
    presentation.mem_fineEdgeSupportFinset_iff_raw,
    presentation.mem_coarseEdgeSupportFinset_iff_raw]
  fin_cases face
  simp [presentation,
    fineChartSupport, coarseChartSupport, faceEdge0, faceEdge1, faceEdge2,
    edgeLeft, edgeRight, coarseRead]

/-- Forgetting selection proofs identifies every selected fine chart with
the corresponding selected coarse chart.  This Cycle 15 API constructor turns
the preceding raw-set equality into the degree-zero reindexing used to build
the actual cochain equivalence; `A` is its only explicit input. -/
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
the corresponding selected coarse edge.  This Cycle 15 API constructor turns
the raw-set equality into the degree-one reindexing used by the actual
comparison, with no supplied map inverse. -/
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
the corresponding selected coarse face.  This Cycle 15 API constructor turns
the raw-set equality into the degree-two reindexing used by the cochain
comparison, with no filling certificate. -/
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

/-- Reindex raw coarse chart cochains onto the corresponding fine charts.
This is the degree-zero API component of the Cycle 15 cochain equivalence,
constructed solely from `selectedChartEquiv`. -/
def rawChartCochainEquiv (A : Finset (Fin 2)) :
    (presentation.CoarseChartIn A → ℚ) ≃ₗ[ℚ]
      (presentation.FineChartIn A → ℚ) :=
  cochainEquivOfIndexEquiv (selectedChartEquiv A)

/-- Reindex raw coarse edge cochains onto the corresponding fine edges.  This
is the degree-one API component of the Cycle 15 cochain equivalence,
constructed solely from `selectedEdgeEquiv`. -/
def rawEdgeCochainEquiv (A : Finset (Fin 2)) :
    (presentation.CoarseEdgeIn A → ℚ) ≃ₗ[ℚ]
      (presentation.FineEdgeIn A → ℚ) :=
  cochainEquivOfIndexEquiv (selectedEdgeEquiv A)

/-- Reindex raw coarse face cochains onto the corresponding fine faces.  This
is the degree-two API component of the Cycle 15 cochain equivalence,
constructed solely from `selectedFaceEquiv`. -/
def rawFaceCochainEquiv (A : Finset (Fin 2)) :
    (presentation.CoarseFaceIn A → ℚ) ≃ₗ[ℚ]
      (presentation.FineFaceIn A → ℚ) :=
  cochainEquivOfIndexEquiv (selectedFaceEquiv A)

/-- Selected edge-left incidence is preserved by the identity cell tables.
This local Cycle 15 API lemma derives endpoint compatibility from raw identity
maps and supports `rawCochainEquiv_comm0`. -/
theorem selectedEquiv_edgeLeft (A : Finset (Fin 2))
    (edge : presentation.FineEdgeIn A) :
    selectedChartEquiv A (presentation.fineEdgeLeftIn A edge) =
      presentation.coarseEdgeLeftIn A (selectedEdgeEquiv A edge) := by
  apply Subtype.ext
  rfl

/-- Selected edge-right incidence is preserved by the identity cell tables.
This local Cycle 15 API lemma derives endpoint compatibility from raw identity
maps and supports `rawCochainEquiv_comm0`. -/
theorem selectedEquiv_edgeRight (A : Finset (Fin 2))
    (edge : presentation.FineEdgeIn A) :
    selectedChartEquiv A (presentation.fineEdgeRightIn A edge) =
      presentation.coarseEdgeRightIn A (selectedEdgeEquiv A edge) := by
  apply Subtype.ext
  rfl

/-- Face-edge zero incidence is preserved by the identity cell tables.  This
local Cycle 15 API lemma comes from raw face incidence and supports the
degree-one differential comparison. -/
theorem selectedEquiv_faceEdge0 (A : Finset (Fin 2))
    (face : presentation.FineFaceIn A) :
    selectedEdgeEquiv A (presentation.fineFaceEdge0In A face) =
      presentation.coarseFaceEdge0In A (selectedFaceEquiv A face) := by
  apply Subtype.ext
  rfl

/-- Face-edge one incidence is preserved by the identity cell tables.  This
local Cycle 15 API lemma comes from raw face incidence and supports the
degree-one differential comparison. -/
theorem selectedEquiv_faceEdge1 (A : Finset (Fin 2))
    (face : presentation.FineFaceIn A) :
    selectedEdgeEquiv A (presentation.fineFaceEdge1In A face) =
      presentation.coarseFaceEdge1In A (selectedFaceEquiv A face) := by
  apply Subtype.ext
  rfl

/-- Face-edge two incidence is preserved by the identity cell tables.  This
local Cycle 15 API lemma comes from raw face incidence and supports the
degree-one differential comparison. -/
theorem selectedEquiv_faceEdge2 (A : Finset (Fin 2))
    (face : presentation.FineFaceIn A) :
    selectedEdgeEquiv A (presentation.fineFaceEdge2In A face) =
      presentation.coarseFaceEdge2In A (selectedFaceEquiv A face) := by
  apply Subtype.ext
  rfl

/-- The raw chart and edge reindexings intertwine degree-zero incidence.  This
is the Cycle 15 degree-zero cochain API used to construct the actual complex
equivalence; all inputs are raw selected cells and an arbitrary cochain. -/
theorem rawCochainEquiv_comm0 (A : Finset (Fin 2))
    (cochain : presentation.CoarseChartIn A → ℚ) :
    rawEdgeCochainEquiv A (presentation.coarseD0LinearMap A cochain) =
      presentation.fineD0LinearMap A (rawChartCochainEquiv A cochain) := by
  funext edge
  change
    presentation.coarseD0LinearMap A cochain (selectedEdgeEquiv A edge) =
      presentation.fineD0LinearMap A (rawChartCochainEquiv A cochain) edge
  rw [presentation.coarseD0LinearMap_apply,
    presentation.fineD0LinearMap_apply]
  change
    cochain (presentation.coarseEdgeRightIn A (selectedEdgeEquiv A edge)) -
        cochain (presentation.coarseEdgeLeftIn A (selectedEdgeEquiv A edge)) =
      cochain (selectedChartEquiv A (presentation.fineEdgeRightIn A edge)) -
        cochain (selectedChartEquiv A (presentation.fineEdgeLeftIn A edge))
  rw [selectedEquiv_edgeRight, selectedEquiv_edgeLeft]

/-- The raw edge and face reindexings intertwine degree-one incidence.  This
is the Cycle 15 degree-one cochain API used to construct the actual complex
equivalence; it assumes no cocycle or rank result. -/
theorem rawCochainEquiv_comm1 (A : Finset (Fin 2))
    (cochain : presentation.CoarseEdgeIn A → ℚ) :
    rawFaceCochainEquiv A (presentation.coarseD1LinearMap A cochain) =
      presentation.fineD1LinearMap A (rawEdgeCochainEquiv A cochain) := by
  funext face
  change
    presentation.coarseD1LinearMap A cochain (selectedFaceEquiv A face) =
      presentation.fineD1LinearMap A (rawEdgeCochainEquiv A cochain) face
  rw [presentation.coarseD1LinearMap_apply,
    presentation.fineD1LinearMap_apply]
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
from the original total identity edge table.  This comparison API discharges
partial-map compatibility from raw table equality, not from a supplied map
certificate. -/
theorem edgeMapOptionIn_eq_some_selected (A : Finset (Fin 2))
    (edge : presentation.FineEdgeIn A) :
    presentation.edgeMapOptionIn A edge = some (selectedEdgeEquiv A edge) := by
  exact (presentation.edgeMapOptionIn_eq_some_iff A edge
    (selectedEdgeEquiv A edge)).2 rfl

/-- Raw degree-one comparison pullback is exactly edge reindexing.  This is
the Cycle 15 comparison-map API connecting the executable partial table to the
degree-one cochain equivalence; `A` and the cochain are its only inputs. -/
theorem edgePullback1_eq_rawEdgeCochainEquiv (A : Finset (Fin 2))
    (cochain : presentation.CoarseEdgeIn A → ℚ) :
    presentation.edgePullback1LinearMap A cochain =
      rawEdgeCochainEquiv A cochain := by
  funext edge
  rw [presentation.edgePullback1LinearMap_apply]
  change (presentation.edgeMapOptionIn A edge).elim 0 cochain =
    cochain (selectedEdgeEquiv A edge)
  rw [edgeMapOptionIn_eq_some_selected]
  rfl

/-! ## Actual selected-complex equivalence -/

/-- Degree-zero equivalence from the actual coarse A-subnerve to the actual
fine canonical-preimage subnerve.  This Cycle 15 data constructor composes the
owner-provided raw/semantic cell equivalences and raw reindexing; no H¹ inverse
is supplied. -/
noncomputable def semanticChartCochainEquiv (A : Finset (Fin 2)) :
    (presentation.coarseSupportedNerve.targetSubsetComplex
        (↑A : Set (Fin 2))).C0 ≃ₗ[ℚ]
      (presentation.fineSupportedNerve.targetSubsetComplex
        (presentation.canonicalFinePreimage A)).C0 :=
  (presentation.coarseChartCochainEquiv A).trans
    ((rawChartCochainEquiv A).trans
      (presentation.fineChartCochainEquiv A).symm)

/-- Degree-one equivalence from the actual coarse A-subnerve to the actual
fine canonical-preimage subnerve.  This Cycle 15 data constructor composes the
owner-provided raw/semantic cell equivalences and raw reindexing; no comparison
inverse is supplied. -/
noncomputable def semanticEdgeCochainEquiv (A : Finset (Fin 2)) :
    (presentation.coarseSupportedNerve.targetSubsetComplex
        (↑A : Set (Fin 2))).C1 ≃ₗ[ℚ]
      (presentation.fineSupportedNerve.targetSubsetComplex
        (presentation.canonicalFinePreimage A)).C1 :=
  (presentation.coarseEdgeCochainEquiv A).trans
    ((rawEdgeCochainEquiv A).trans
      (presentation.fineEdgeCochainEquiv A).symm)

/-- Degree-two equivalence from the actual coarse A-subnerve to the actual
fine canonical-preimage subnerve.  This Cycle 15 data constructor composes the
owner-provided raw/semantic cell equivalences and raw reindexing; no filling
certificate is supplied. -/
noncomputable def semanticFaceCochainEquiv (A : Finset (Fin 2)) :
    (presentation.coarseSupportedNerve.targetSubsetComplex
        (↑A : Set (Fin 2))).C2 ≃ₗ[ℚ]
      (presentation.fineSupportedNerve.targetSubsetComplex
        (presentation.canonicalFinePreimage A)).C2 :=
  (presentation.coarseFaceCochainEquiv A).trans
    ((rawFaceCochainEquiv A).trans
      (presentation.fineFaceCochainEquiv A).symm)

/-- The actual degree-zero differentials commute with the generated
degreewise equivalences.  This Cycle 15 API lemma lifts raw `d0` compatibility
through canonical A-subnerve coordinates and supplies the first commutation
field of `semanticCochainEquiv`. -/
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
degreewise equivalences.  This Cycle 15 API lemma lifts raw `d1` compatibility
through canonical A-subnerve coordinates and supplies the second commutation
field of `semanticCochainEquiv`. -/
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
for every finite coarse target subset.  This Cycle 15 data bridge converts raw
incidence compatibility into semantic H¹ data; its commutation fields are
discharged by the preceding theorems rather than certificate fields. -/
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
of the generated cochain equivalence.  This Cycle 15 API theorem ties the
constructed equivalence to the canonical map required by the GOAL, using the
raw partial-map theorem rather than an arbitrary isomorphism. -/
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
the H1 map induced by the generated cochain equivalence.  This Cycle 15 API
theorem lifts the actual `f1` equality to literal quotient H¹ via the existing
`ThreeCochainComplex` quotient API. -/
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
bijective, including the empty subset.  This is the all-subset Cycle 15
semantic lemma supporting uniformity; bijectivity comes from the constructed
cochain equivalence, not stored inverse or rank data. -/
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

/-- Every finite target subset has zero literal and executable H1 defect.
This checker-facing Cycle 15 API combines actual-map bijectivity with the
generic Cycle 8 correctness theorem and adds no expected defect field. -/
theorem all_computedASubnerveDefects_zero (A : Finset (Fin 2)) :
    presentation.computedASubnerveDefect A = (0, 0) := by
  rw [presentation.computedASubnerveDefect_eq_aSubnerveDefect]
  exact
    (presentation.toGeometry.aSubnerveDefect_eq_zero_iff_bijective
      (↑A : Set (Fin 2))).2
      (aSubnerveComparisonHom_h1Map_bijective A)

/-- The generic all-subset uniformity checker accepts the raw R1 table.  This
Cycle 15 firing theorem follows from the generic checker iff and the
all-subset actual-map proof, not from an opaque result bit. -/
theorem uniformPresentationCheck_true :
    presentation.uniformPresentationCheck = true := by
  apply
    (presentation.uniformPresentationCheck_eq_true_iff_allNonemptyDefects).2
  intro A _hA
  exact all_computedASubnerveDefects_zero A

/-- The exact R1 presentation is uniformly invariant for every finite law
family adequate for both readings.  This is the Cycle 15 main uniformity
component: generic checker soundness preserves the internal law-family and
adequacy quantifiers. -/
theorem uniformPresentation : UniformPresentation presentation :=
  presentation.uniformPresentationCheck_eq_true_iff.mp
    uniformPresentationCheck_true

/-! ## Direct C3 failure on target zero -/

/-- The unique coarse chart selected by target zero.  This private Cycle 15
fixture datum is computed from raw selection and anchors the fiber constraint;
it is not a supplied C3 witness. -/
def coarseChartZero : presentation.CoarseChartIn targetZero :=
  ⟨(0 : Fin 3), by decide⟩

/-- The unique fine self-loop selected over target zero.  This private Cycle
15 fixture datum is computed from raw selection and names the cycle support. -/
def fineEdgeZero : presentation.FineEdgeIn targetZero :=
  ⟨(0 : Fin 3), by decide⟩

/-- Constant coefficient one on the selected fine self-loop.  This explicit
Cycle 15 test chain is the input to the raw C3 constraint/nonboundary proofs,
not a stored condition result. -/
def loopChain : presentation.FineEdgeIn targetZero → ℚ :=
  fun _ => 1

/-- Every fine chart selected over target zero is chart zero.  This private
Cycle 15 normalization API derives from the public raw-selection
characterization and supports the fiber-cycle proof. -/
theorem fineChartAtTargetZero_eq_zero
    (chart : presentation.FineChartIn targetZero) : chart.1 = (0 : Fin 3) := by
  rcases chart with ⟨chart, hmem⟩
  have hselected :=
    (presentation.mem_fineChartsIn_iff_raw targetZero chart).1 hmem
  rw [computedFactor_eq_coarseRead] at hselected
  fin_cases chart <;>
    simp [presentation, fineChartSupport, coarseRead, targetZero] at hselected ⊢

/-- Every fine edge selected over target zero is edge zero.  This private
Cycle 15 normalization API derives from raw support and supports both cycle
conservation and the H¹ nonvacuity route. -/
theorem fineEdgeAtTargetZero_eq_zero
    (edge : presentation.FineEdgeIn targetZero) : edge.1 = (0 : Fin 3) := by
  rcases edge with ⟨edge, hmem⟩
  have hselected :=
    (presentation.mem_fineEdgesIn_iff_raw targetZero edge).1 hmem
  simp only [presentation.mem_fineEdgeSupportFinset_iff_raw] at hselected
  rw [computedFactor_eq_coarseRead] at hselected
  fin_cases edge <;>
    simp [presentation, fineChartSupport, edgeLeft, edgeRight, coarseRead,
      targetZero] at hselected ⊢

/-- The selected self-loop satisfies the raw fiber-cycle constraint.  This is
the Cycle 15 direct C3-failure API premise, proved from raw endpoints and the
public constraint evaluation formulas rather than assumed as a certificate. -/
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

/-- No fine face is selected by target zero.  This Cycle 15 raw-selection API
provides the direct obstruction to an internal-face filling and is derived
from the canonical support table. -/
theorem noFineFaceAtTargetZero
    (face : presentation.FineFaceIn targetZero) : False := by
  rcases face with ⟨face, hmem⟩
  have hselected :=
    (presentation.mem_fineFacesIn_iff_raw targetZero face).1 hmem
  simp only [presentation.mem_fineFaceSupportFinset_iff_raw,
    presentation.mem_fineEdgeSupportFinset_iff_raw] at hselected
  rw [computedFactor_eq_coarseRead] at hselected
  fin_cases face
  simp [presentation, fineChartSupport, faceEdge0, faceEdge1, faceEdge2,
    edgeLeft, edgeRight, coarseRead, targetZero] at hselected

/-! ## Nonzero H1 on the same target-zero block -/

/-- The actual coarse constant-rational complex on target zero.  This
abbreviation positions the existing semantic A-subnerve complex in the Cycle
15 nonvacuity proof and adds no structure or premise. -/
abbrev coarseTargetZeroComplex : ThreeCochainComplex ℚ :=
  presentation.coarseSupportedNerve.targetSubsetComplex
    (↑targetZero : Set (Fin 2))

/-- The actual fine constant-rational complex on the canonical preimage of
target zero.  This abbreviation positions the existing semantic preimage
complex in the Cycle 15 nonvacuity proof and adds no structure or premise. -/
abbrev fineTargetZeroComplex : ThreeCochainComplex ℚ :=
  presentation.fineSupportedNerve.targetSubsetComplex
    (presentation.canonicalFinePreimage targetZero)

/-- The unique selected raw coarse self-loop at target zero.  This private
Cycle 15 fixture datum is generated by raw selection and feeds the canonical
raw-to-semantic edge equivalence. -/
def coarseEdgeZero : presentation.CoarseEdgeIn targetZero :=
  ⟨(0 : Fin 3), by decide⟩

/-- The corresponding actual selected coarse self-loop.  This Cycle 15 datum
is obtained through the owner-provided raw/semantic edge equivalence and is
the evaluation point for the period argument. -/
def coarseActualEdgeZero :
    presentation.coarseSupportedNerve.EdgeInTargetSubset
      (↑targetZero : Set (Fin 2)) :=
  presentation.coarseEdgeEquiv targetZero coarseEdgeZero

/-- No coarse face is selected by target zero.  This private Cycle 15 API
transports the already proved fine-face absence through the selected-face
equivalence; it assumes no semantic H¹ result. -/
theorem noCoarseFaceAtTargetZero
    (face : presentation.CoarseFaceIn targetZero) : False := by
  exact noFineFaceAtTargetZero
    ((selectedFaceEquiv targetZero).symm face)

/-- Evaluation on the isolated target-zero self-loop.  This Cycle 15 linear
functional is built from the actual selected edge and detects the quotient H¹
class without storing a nonzero certificate. -/
def coarseTargetZeroPeriod (cochain : coarseTargetZeroComplex.C1) : ℚ :=
  cochain coarseActualEdgeZero

/-- Every actual coarse coboundary has zero target-zero loop period.  This
Cycle 15 API lemma derives from equality of the actual self-loop endpoints and
is the descent obstruction used in the quotient nonzero proof. -/
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

/-- Constant coefficient one on the actual coarse target-zero self-loop.
This explicit Cycle 15 cochain is constructed on the semantic complex and
serves as the nonvacuity witness; it is not presentation data. -/
def coarseTargetZeroCochain : coarseTargetZeroComplex.C1 :=
  fun _ => 1

/-- The target-zero self-loop cochain is an actual cocycle.  This Cycle 15 API
lemma uses the proved absence of selected coarse faces and supplies the kernel
membership for the quotient class. -/
theorem coarseTargetZeroCochain_cocycle :
    coarseTargetZeroComplex.d1 coarseTargetZeroCochain = 0 := by
  funext face
  exact (noCoarseFaceAtTargetZero
    ((presentation.coarseFaceEquiv targetZero).symm face)).elim

/-- The target-zero cocycle as an element of the actual kernel.  This Cycle 15
data constructor packages `coarseTargetZeroCochain_cocycle`; its kernel proof
is discharged immediately rather than supplied externally. -/
def coarseTargetZeroCycle : LinearMap.ker coarseTargetZeroComplex.d1 :=
  ⟨coarseTargetZeroCochain, coarseTargetZeroCochain_cocycle⟩

/-- The actual quotient-H1 class of the isolated self-loop.  This Cycle 15
data constructor applies the existing literal quotient map to the explicit
cycle and carries no assumed nonzeroness. -/
def coarseTargetZeroClass : coarseTargetZeroComplex.H1 :=
  (LinearMap.range coarseTargetZeroComplex.boundaryToCycles).mkQ
    coarseTargetZeroCycle

/-- The displayed target-zero cocycle has unit period.  This private Cycle 15
normalization lemma evaluates the explicit chain and is used only to prove the
quotient class nonzero. -/
theorem coarseTargetZeroPeriod_cycle :
    coarseTargetZeroPeriod coarseTargetZeroCycle.1 = 1 := by
  rfl

/-- The actual coarse target-zero quotient class is nonzero.  This is the
Cycle 15 coarse nonvacuity theorem: coboundary period zero and cycle period one
discharge the claim in the literal quotient. -/
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

/-- The coarse target-zero H1 space has positive finite dimension.  This
Cycle 15 nonvacuity API converts the explicit nonzero quotient class to the
finrank condition required by the fixed GOAL. -/
theorem targetZero_coarse_h1_pos :
    0 < Module.finrank ℚ coarseTargetZeroComplex.H1 :=
  Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨coarseTargetZeroClass, coarseTargetZeroClass_ne_zero⟩

/-- The actual fine class obtained from the canonical target-zero comparison.
This Cycle 15 datum is the image under the actual `h1Map`, so it records no
independently supplied fine cohomology witness. -/
def fineTargetZeroClass : fineTargetZeroComplex.H1 :=
  (presentation.toGeometry.aSubnerveComparisonHom
    (↑targetZero : Set (Fin 2))).h1Map coarseTargetZeroClass

/-- The fine canonical image is nonzero by actual comparison injectivity.
This Cycle 15 nonvacuity API uses the all-subset actual-map theorem and the
coarse class, tying both sides to the same comparison. -/
theorem fineTargetZeroClass_ne_zero : fineTargetZeroClass ≠ 0 := by
  intro hzero
  apply coarseTargetZeroClass_ne_zero
  apply (aSubnerveComparisonHom_h1Map_bijective targetZero).1
  simpa only [fineTargetZeroClass, map_zero] using hzero

/-- The fine canonical-preimage H1 space has positive finite dimension.  This
Cycle 15 nonvacuity API converts the canonical image's nonzeroness to the
finrank condition required by the fixed GOAL. -/
theorem targetZero_fine_h1_pos :
    0 < Module.finrank ℚ fineTargetZeroComplex.H1 :=
  Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨fineTargetZeroClass, fineTargetZeroClass_ne_zero⟩

/-- Both sides of the same C3-failing target-zero comparison have nonzero H1.
This is the Cycle 15 paired nonvacuity theorem used by the main witness; both
components are discharged by the explicit quotient class and actual map. -/
theorem targetZero_both_h1_pos :
    0 < Module.finrank ℚ coarseTargetZeroComplex.H1 ∧
      0 < Module.finrank ℚ fineTargetZeroComplex.H1 :=
  ⟨targetZero_coarse_h1_pos, targetZero_fine_h1_pos⟩

/-- The target-zero loop is not in the image of the internal-face boundary.
This Cycle 15 direct obstruction theorem combines the explicit nonzero chain
with raw selected-face absence and assumes no failed-checker bit. -/
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

/-- Raw C3 fails at target zero.  This Cycle 15 obstruction theorem applies the
raw C3 elimination rule to the explicit cycle/nonboundary pair; there is no
condition result or filling certificate premise. -/
theorem not_rawConditionC3At :
    ¬ presentation.RawConditionC3At targetZero := by
  intro hraw
  exact loopChain_not_internalFaceImage
    (hraw coarseChartZero loopChain loopChain_constraint)

/-- The executable C3 checker rejects target zero.  This Cycle 15 checker API
uses generic soundness against the independently proved raw failure, not a
stored expected Boolean. -/
theorem conditionC3AtTargetSubsetCheck_false :
    presentation.conditionC3AtTargetSubsetCheck targetZero = false := by
  cases hcheck : presentation.conditionC3AtTargetSubsetCheck targetZero
  · rfl
  · exfalso
    exact not_rawConditionC3At
      ((presentation.conditionC3AtTargetSubsetCheck_eq_true_iff_raw
        targetZero).1 hcheck)

/-- Semantic C3 fails on the actual canonical target-zero A-subnerve.  This is
the Cycle 15 semantic failure component, transported through the generic raw/
actual iff from the explicit cycle obstruction. -/
theorem not_conditionC3AtTargetSubset :
    ¬ presentation.toGeometry.ConditionC3AtTargetSubset
      (↑targetZero : Set (Fin 2)) := by
  intro hsemantic
  exact not_rawConditionC3At
    ((presentation.rawConditionC3At_iff_conditionC3AtTargetSubset
      targetZero).2 hsemantic)

/-- Hence the geometric all-subset Condition C predicate fails directly at
its target-zero C3 projection.  This Cycle 15 Atlas-locus theorem uses the
actual `ConditionCAllA` projection at the same nonempty subset, without
reversing the sufficient-condition bridge. -/
theorem not_conditionCAllA : ¬ presentation.toGeometry.ConditionCAllA := by
  intro hAllA
  exact not_conditionC3AtTargetSubset
    (TargetSupportedNerveMorphism.ConditionCAllA.conditionC3At
      presentation.toGeometry hAllA (↑targetZero : Set (Fin 2))
      targetZero_nonempty)

/-- The generic all-clause checker rejects the same raw presentation.  This
Cycle 15 checker-facing theorem follows from the generic checker iff and the
direct semantic failure, not from an answer field. -/
theorem conditionCAllACheck_false :
    presentation.conditionCAllACheck = false := by
  cases hcheck : presentation.conditionCAllACheck
  · rfl
  · exfalso
    exact not_conditionCAllA
      ((presentation.conditionCAllACheck_eq_true_iff).1 hcheck)

/-! ## The same failure under a nonconstant indicator law -/

/-- The target-zero Boolean indicator family on the coarse reading.  This
Cycle 15 datum invokes the generic indicator construction on the explicit
subset and supplies no selected law values. -/
noncomputable def indicatorLaws : FiniteLawFamily presentation.Source :=
  indicatorLawFamily presentation.coarseReading
    (↑targetZero : Set (Fin 2))

/-- Canonical adequacy of the target-zero indicator on the coarse reading.
This Cycle 15 API discharges the coarse adequacy premise using the generic
indicator theorem for the explicit subset. -/
theorem indicatorCoarseAdequate :
    indicatorLaws.Adequate presentation.coarseReading :=
  indicatorLawFamily_adequate presentation.coarseReading
    (↑targetZero : Set (Fin 2))

/-- Canonical adequacy of the same indicator on the fine reading.  This Cycle
15 API discharges fine adequacy via the generic coarser-reading theorem and
the presentation's proved reading relation. -/
theorem indicatorFineAdequate :
    indicatorLaws.Adequate presentation.fineReading :=
  indicatorLawFamily_adequate_of_coarserThan presentation.coarseReading
    presentation.fineReading presentation.coarserThan
    (↑targetZero : Set (Fin 2))

/-- The source-generated true label of the target-zero indicator.  This Cycle
15 datum comes from the generic generated-label construction and explicit
subset nonemptiness; no label is supplied as a certificate. -/
noncomputable def indicatorLabel : LawValueLabel indicatorLaws :=
  indicatorLawFamilyTrueLabel presentation.coarseReading
    (↑targetZero : Set (Fin 2)) targetZero_nonempty

/-- The indicator law genuinely distinguishes sources zero and two.  This is
the Cycle 15 nondegeneracy theorem, computed directly from raw readings and the
indicator definition rather than assumed. -/
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

/-- Law-indexed C3 fails at the source-generated true indicator label.  This
Cycle 15 bridge theorem uses the generated-fiber equality and the proved
reverse C3 transport to reduce an assumed law-block filling to the actual
target-zero contradiction. -/
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

/-- The full law-indexed C3 clause fails for the nonconstant indicator family.
This Cycle 15 API projects a hypothetical all-label clause to the generated
true label; adequacy and label data are already discharged above. -/
theorem indicator_not_conditionC3 :
    ¬ presentation.toGeometry.ConditionC3 indicatorLaws
      indicatorCoarseAdequate indicatorFineAdequate := by
  intro hC3
  exact indicator_not_conditionC3At (hC3 indicatorLabel)

/-! ## Bounded R1 necessity conclusion -/

/-- Exact C3 non-necessity witness: one raw presentation is uniformly
invariant, fails both the law-free and nonconstant-law C3 clauses at the same
target-zero block, and has nonzero H1 on both sides of that block.  This is the
Cycle 15 main theorem corresponding to the fixed GOAL witness obligation; all
components are assembled from the named uniformity, failure, and literal H¹
nonvacuity theorems and it has no external premise. -/
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
