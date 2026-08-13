import ResearchLean.AG.UniformInvariance.GLocalV1V5Reduction
import Formal.Util.AssertStandardAxioms

/-!
# Registered T3/T6 witnesses for the permanent `G_local-v1` observation

This module transfers the two preregistered Round-15
identity-split inputs `TERNARY-CYCLE-3` and `TERNARY-CYCLE-6` into raw finite
comparison presentations.  It supplies the route-integrity input consumed by
the companion `GLocalV1T3T6Observation` evaluation by proving that every
registered nonempty scope is already irreducible under the full permanent
packet kernel.

The presentations contain only explicit readings, finite cell tables,
incidence, supports, and identity partial cell maps.  They do not contain the
computed factor, reducer states, terminal packets, observation, ranks,
defects, checker values, or semantic labels.  The registered name-free
structural SHA-256 values are
`452517a5dd3df09eea96f4de0c0b737f274384c239267aeba2d5ba06fda616a2`
for T3 and
`0e92de476cd0af4dbeb80290afff463354da87c01c4548bab5d7806927d1d180`
for T6; they are documentation locators and occur in no Lean definition or
proof premise.

## Implementation notes

Both registered inputs have the same identity-split target geometry.  A
shared raw constructor carries that geometry while the two public
presentations supply their different face tables.  Packet emptiness is not
decided by enumerating higher-order assignment spaces: definition-owner
elimination theorems reduce it to the four raw table facts excluding v4
coarse, v4 fine-only, coordinate, and doubled-cycle packets.  Expected
observation data and semantic labels are deliberately absent from these raw
fixture presentations.
-/

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology TwoPhase
open FiniteComparisonPresentation

namespace GLocalV1T3T6Witnesses

/-! ## Registered raw inputs -/

/-- Canonical coarse reading `[0,0,1]` realizing the registered proper factor.

Position: raw-input definition for the T3/T6 transfer in fixed GOAL claim
(v)(a).  It is computed from the explicit `Fin 3` source and carries no
factor, observation, or semantic-label certificate. -/
def coarseRead (source : Fin 3) : Fin 2 :=
  if source = 2 then 1 else 0

/-- Coarse identity-split chart supports `[{0},{0,1}]`.

Position: raw-input definition for the registered T3/T6 presentations.  The
support table comes from the permanent structural payload and contains no
reducer, observation, rank, or checker result. -/
def coarseChartSupport (chart : Fin 2) : Finset (Fin 2) :=
  if chart = 0 then {0} else {0, 1}

/-- Fine identity-split chart supports `[{0,1},{2}]`.

Position: raw-input definition for the registered T3/T6 presentations.  The
support table is structural payload data and contains no derived observation
or semantic label. -/
def fineChartSupport (chart : Fin 2) : Finset (Fin 3) :=
  if chart = 0 then {0, 1} else {2}

/-- Every registered edge is a self-loop at chart zero for index zero and at
chart one otherwise.

Position: raw-incidence definition shared by the T3/T6 presentations.  Its
only input is a finite edge index; no condition or cohomology result is
supplied. -/
def edgeChart {neutralEdgeCount : Nat}
    (edge : Fin (neutralEdgeCount + 1)) : Fin 2 :=
  if edge = 0 then 0 else 1

/-- Shared raw constructor for the two registered identity-split inputs.

Position: shared raw-presentation constructor for fixed GOAL claim (v)(a).
The face functions and their non-anchor proofs are finite incidence input;
all factor, reduction, observation, defect, and label data remain conclusions
of the public kernels. -/
def identitySplitPresentation
    (neutralEdgeCount faceCount : Nat)
    (faceEdge0 faceEdge1 faceEdge2 :
      Fin faceCount → Fin (neutralEdgeCount + 1))
    (hfaceEdge0 : ∀ face, faceEdge0 face ≠ 0)
    (hfaceEdge1 : ∀ face, faceEdge1 face ≠ 0)
    (hfaceEdge2 : ∀ face, faceEdge2 face ≠ 0) :
    FiniteComparisonPresentation where
  Source := Fin 3
  sourceFintype := inferInstance
  sourceDecidableEq := inferInstance
  sourceDefault := 0
  sourceEntries := List.finRange 3
  source_mem_sourceEntries := by intro source; simp
  CoarseTarget := Fin 2
  coarseTargetFintype := inferInstance
  coarseTargetDecidableEq := inferInstance
  coarseTargetEntries := List.finRange 2
  coarseTarget_mem_coarseTargetEntries := by intro target; simp
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
  CoarseEdge := Fin (neutralEdgeCount + 1)
  coarseEdgeFintype := inferInstance
  coarseEdgeDecidableEq := inferInstance
  coarseEdgeEntries := List.finRange (neutralEdgeCount + 1)
  coarseEdge_mem_coarseEdgeEntries := by intro edge; simp
  CoarseFace := Fin faceCount
  coarseFaceFintype := inferInstance
  coarseFaceDecidableEq := inferInstance
  coarseFaceEntries := List.finRange faceCount
  coarseFace_mem_coarseFaceEntries := by intro face; simp
  coarseEdgeLeft := edgeChart
  coarseEdgeRight := edgeChart
  coarseFaceEdge0 := faceEdge0
  coarseFaceEdge1 := faceEdge1
  coarseFaceEdge2 := faceEdge2
  coarseFaceEdge0_left := by
    intro face
    simp [edgeChart, hfaceEdge0 face, hfaceEdge1 face]
  coarseFaceEdge0_right := by
    intro face
    simp [edgeChart, hfaceEdge0 face, hfaceEdge2 face]
  coarseFaceEdge1_right := by
    intro face
    simp [edgeChart, hfaceEdge1 face, hfaceEdge2 face]
  coarseChartSupport := coarseChartSupport
  coarseChartSupport_nonempty := by
    intro chart
    fin_cases chart <;> simp [coarseChartSupport]
  FineChart := Fin 2
  fineChartFintype := inferInstance
  fineChartDecidableEq := inferInstance
  fineChartEntries := List.finRange 2
  fineChart_mem_fineChartEntries := by intro chart; simp
  FineEdge := Fin (neutralEdgeCount + 1)
  fineEdgeFintype := inferInstance
  fineEdgeDecidableEq := inferInstance
  fineEdgeEntries := List.finRange (neutralEdgeCount + 1)
  fineEdge_mem_fineEdgeEntries := by intro edge; simp
  FineFace := Fin faceCount
  fineFaceFintype := inferInstance
  fineFaceDecidableEq := inferInstance
  fineFaceEntries := List.finRange faceCount
  fineFace_mem_fineFaceEntries := by intro face; simp
  fineEdgeLeft := edgeChart
  fineEdgeRight := edgeChart
  fineFaceEdge0 := faceEdge0
  fineFaceEdge1 := faceEdge1
  fineFaceEdge2 := faceEdge2
  fineFaceEdge0_left := by
    intro face
    simp [edgeChart, hfaceEdge0 face, hfaceEdge1 face]
  fineFaceEdge0_right := by
    intro face
    simp [edgeChart, hfaceEdge0 face, hfaceEdge2 face]
  fineFaceEdge1_right := by
    intro face
    simp [edgeChart, hfaceEdge1 face, hfaceEdge2 face]
  fineChartSupport := fineChartSupport
  fineChartSupport_nonempty := by
    intro chart
    fin_cases chart <;> simp [fineChartSupport]
  chartMap := id
  edgeMap := some
  faceMap := some
  edge_some_left := by
    intro fineEdge coarseEdge hmap
    have hequal := Option.some.inj hmap
    subst coarseEdge
    rfl
  edge_some_right := by
    intro fineEdge coarseEdge hmap
    have hequal := Option.some.inj hmap
    subst coarseEdge
    rfl
  edge_none_fiber := by intro fineEdge hmap; simp at hmap
  face_some_edge0 := by
    intro fineFace coarseFace hmap
    have hequal := Option.some.inj hmap
    subst coarseFace
    rfl
  face_some_edge1 := by
    intro fineFace coarseFace hmap
    have hequal := Option.some.inj hmap
    subst coarseFace
    rfl
  face_some_edge2 := by
    intro fineFace coarseFace hmap
    have hequal := Option.some.inj hmap
    subst coarseFace
    rfl
  face_none_edge0 := by intro fineFace hmap; simp at hmap
  face_none_edge1 := by intro fineFace hmap; simp at hmap
  face_none_edge2 := by intro fineFace hmap; simp at hmap
  chartSupport_compatible_source := by
    intro fineChart source hsource
    fin_cases fineChart <;> fin_cases source <;>
      simp [fineChartSupport, coarseChartSupport, coarseRead] at hsource ⊢

/-- Slot-zero face incidence for the registered ternary 3-cycle.

Position: raw T3 face-table definition transferred from the permanent
Round-15 payload.  It supplies incidence only, not a reduction or observation
certificate. -/
def t3FaceEdge0 (face : Fin 3) : Fin 4 :=
  if face = 0 then 1 else if face = 1 then 2 else 3

/-- Slot-one face incidence for the registered ternary 3-cycle.

Position: raw T3 face-table definition transferred from the permanent
Round-15 payload; no conclusion-equivalent data is stored. -/
def t3FaceEdge1 (face : Fin 3) : Fin 4 :=
  if face = 0 then 2 else if face = 1 then 3 else 1

/-- Slot-two face incidence for the registered ternary 3-cycle.

Position: raw T3 face-table definition transferred from the permanent
Round-15 payload; no conclusion-equivalent data is stored. -/
def t3FaceEdge2 (face : Fin 3) : Fin 4 :=
  if face = 0 then 3 else if face = 1 then 1 else 2

/-- Slot-zero face incidence for the registered ternary 6-cycle.

Position: raw T6 face-table definition transferred from the permanent
Round-15 payload; no reduction or semantic-label certificate is supplied. -/
def t6FaceEdge0 (face : Fin 6) : Fin 7 :=
  if face = 0 then 1 else if face = 1 then 2 else if face = 2 then 3 else
    if face = 3 then 4 else if face = 4 then 5 else 6

/-- Slot-one face incidence for the registered ternary 6-cycle.

Position: raw T6 face-table definition transferred from the permanent
Round-15 payload; no conclusion-equivalent data is stored. -/
def t6FaceEdge1 (face : Fin 6) : Fin 7 :=
  if face = 0 then 2 else if face = 1 then 3 else if face = 2 then 4 else
    if face = 3 then 5 else if face = 4 then 6 else 1

/-- Slot-two face incidence for the registered ternary 6-cycle.

Position: raw T6 face-table definition transferred from the permanent
Round-15 payload; no conclusion-equivalent data is stored. -/
def t6FaceEdge2 (face : Fin 6) : Fin 7 :=
  if face = 0 then 3 else if face = 1 then 4 else if face = 2 then 5 else
    if face = 3 then 6 else if face = 4 then 1 else 2

/-- Raw finite presentation of preregistered `TERNARY-CYCLE-3`.

Position: primary structural witness for fixed GOAL claim (v)(a).  Its fields
contain only the registered raw tables and well-formedness proofs; factor,
observation, defect, checker truth, and uniformity remain derived. -/
def t3Presentation : FiniteComparisonPresentation :=
  identitySplitPresentation 3 3 t3FaceEdge0 t3FaceEdge1 t3FaceEdge2
    (by intro face; fin_cases face <;> decide)
    (by intro face; fin_cases face <;> decide)
    (by intro face; fin_cases face <;> decide)

/-- Raw finite presentation of preregistered `TERNARY-CYCLE-6`.

Position: primary structural witness for fixed GOAL claim (v)(a).  Its fields
contain only the registered raw tables and well-formedness proofs; factor,
observation, defect, checker truth, and uniformity remain derived. -/
def t6Presentation : FiniteComparisonPresentation :=
  identitySplitPresentation 6 6 t6FaceEdge0 t6FaceEdge1 t6FaceEdge2
    (by intro face; fin_cases face <;> decide)
    (by intro face; fin_cases face <;> decide)
    (by intro face; fin_cases face <;> decide)

/-! ## Structural-transfer and terminal fast-path facts -/

/-- The first nonempty coarse-target scope shared by both registered inputs.

Position: closed scope input for claim (v)(b)–(c).  It is the literal singleton
`{0}` and carries no defect, observation, or label result. -/
def targetZero : Finset (Fin 2) := {0}

/-- The second nonempty coarse-target scope shared by both registered inputs.

Position: closed scope input for claim (v)(b)–(c).  It is the literal singleton
`{1}` and carries no defect, observation, or label result. -/
def targetOne : Finset (Fin 2) := {1}

/-- The full nonempty coarse-target scope shared by both registered inputs.

Position: closed scope input for claim (v)(b)–(c).  It is computed as the full
finite target and carries no defect, observation, or label result. -/
def targetFull : Finset (Fin 2) := Finset.univ

/-- The T3 executable factor is the canonical raw reading `[0,0,1]`.

Position: registered structural-transfer API for claim (v)(a), normalizing a
computed presentation projection to the literal raw table.  The proof reads
the explicit Source enumeration/readings and no SHA, observation, checker, or
semantic label. -/
@[simp] theorem t3_computedFactor_apply (target : Fin 3) :
    t3Presentation.computedFactor target = coarseRead target := by
  fin_cases target <;> decide

/-- The T6 executable factor is the canonical raw reading `[0,0,1]`.

Position: registered structural-transfer API for claim (v)(a), normalizing a
computed presentation projection to the literal raw table.  The proof reads
the explicit Source enumeration/readings and no SHA, observation, checker, or
semantic label. -/
@[simp] theorem t6_computedFactor_apply (target : Fin 3) :
    t6Presentation.computedFactor target = coarseRead target := by
  fin_cases target <;> decide

/-- Fine targets zero and one occur together in every scoped T3 chart support.

Position: fixture-owner support symmetry API for fixed GOAL claim (v)(a).
The symmetry follows from the registered support table and canonical factor
`[0,0,1]`; no relabel result, observation, or semantic label is assumed. -/
theorem t3_fineChartSupport_zero_iff_one
    (A : Finset t3Presentation.CoarseTarget)
    (chart : t3Presentation.FineChart) :
    (⟨0, by omega⟩ : Fin 3) ∈
        t3Presentation.gLocalV1FineChartSupport A chart ↔
      (⟨1, by omega⟩ : Fin 3) ∈
        t3Presentation.gLocalV1FineChartSupport A chart := by
  rw [t3Presentation.gLocalV1FineChartSupport_apply,
    t3Presentation.gLocalV1FineScopeTargets_apply]
  simp_rw [t3_computedFactor_apply]
  change Fin 2 at chart
  fin_cases chart <;>
    simp [t3Presentation, identitySplitPresentation, fineChartSupport,
      coarseRead]

/-- Fine targets zero and one occur together in every scoped T6 chart support.

Position: fixture-owner support symmetry API for fixed GOAL claim (v)(a).
The symmetry follows from the registered support table and canonical factor
`[0,0,1]`; no relabel result, observation, or semantic label is assumed. -/
theorem t6_fineChartSupport_zero_iff_one
    (A : Finset t6Presentation.CoarseTarget)
    (chart : t6Presentation.FineChart) :
    (⟨0, by omega⟩ : Fin 3) ∈
        t6Presentation.gLocalV1FineChartSupport A chart ↔
      (⟨1, by omega⟩ : Fin 3) ∈
        t6Presentation.gLocalV1FineChartSupport A chart := by
  rw [t6Presentation.gLocalV1FineChartSupport_apply,
    t6Presentation.gLocalV1FineScopeTargets_apply]
  simp_rw [t6_computedFactor_apply]
  change Fin 2 at chart
  fin_cases chart <;>
    simp [t6Presentation, identitySplitPresentation, fineChartSupport,
      coarseRead]

/-- Distinct T3 faces have distinct coarse FaceTwin keys in every scope.

Position: fixture-normalization API supporting the structural packet exclusion
for claim (v)(a).  Injectivity is derived from the registered slot-zero face
table and does not assume packet emptiness, an observation, or a label. -/
theorem t3_faceKey_injective (A : Finset (Fin 2)) :
    Function.Injective (t3Presentation.gLocalV1CoarseFaceKey A) := by
  intro left right hequal
  have hedge := congrArg GLocalV1CoarseFaceTwinKey.edge0 hequal
  fin_cases left <;> fin_cases right <;>
    simp [t3Presentation, identitySplitPresentation, t3FaceEdge0] at hedge ⊢

/-- Every T3 face is selected by every nonempty registered target scope.

Position: fixture-normalization API for the T3 packet-exclusion proof in
claim (v)(a).  The premise is exactly nonemptiness of the explicit coarse
target scope; no reducer result or expected observation is supplied. -/
theorem t3_face_mem_coarseFaces_of_nonempty (A : Finset (Fin 2))
    (hA : A.Nonempty) (face : Fin 3) :
    face ∈ t3Presentation.gLocalV1CoarseFaces A := by
  rw [t3Presentation.mem_gLocalV1CoarseFaces_iff_raw]
  obtain ⟨target, htarget⟩ := hA
  refine ⟨target, ?_⟩
  fin_cases face <;> fin_cases target <;>
    simpa [t3Presentation, identitySplitPresentation, t3FaceEdge0,
      t3FaceEdge1, t3FaceEdge2, edgeChart, coarseChartSupport] using htarget

/-- A nonzero T3 signed face coefficient occurs in a second face.

Position: raw finite-incidence lemma excluding singleton coarse occurrences
in the T3 initial state for claim (v)(a).  It uses only the registered three
face rows and does not consume a packet, terminal, or observation value. -/
theorem t3_face_has_other_occurrence (face : Fin 3) (edge : Fin 4)
    (hcoeff : gLocalV1SignedCoefficient
      (t3FaceEdge0 face) (t3FaceEdge1 face) (t3FaceEdge2 face) edge ≠ 0) :
    ∃ other : Fin 3, other ≠ face ∧
      (t3FaceEdge0 other = edge ∨ t3FaceEdge1 other = edge ∨
        t3FaceEdge2 other = edge) := by
  fin_cases face <;> fin_cases edge <;>
    simp [gLocalV1SignedCoefficient,
      t3FaceEdge0, t3FaceEdge1, t3FaceEdge2] at hcoeff ⊢ <;> decide

/-- The T3 initial state has no packet at any nonempty target scope.

Position: primary T3 route-integrity theorem for claim (v)(a).  It applies
the definition-owner packet-family eliminator to raw incidence/support facts;
it neither enumerates assignment spaces nor supplies an expected terminal,
observation, defect, checker result, or semantic label. -/
theorem t3_initial_packet_empty_of_nonempty (A : Finset (Fin 2))
    (hA : A.Nonempty) :
    t3Presentation.gLocalV1PacketVariants A
      (t3Presentation.gLocalV1InitialState A) = ∅ := by
  apply t3Presentation.gLocalV1PacketVariants_eq_empty_of_face_support
  · intro key hkey edge _hedge hcondition
    obtain ⟨face, hface, rfl⟩ :=
      (t3Presentation.mem_gLocalV1InitialState_coarseFaceClasses_iff A key).1 hkey
    have hcoeff : gLocalV1SignedCoefficient
        (t3FaceEdge0 face) (t3FaceEdge1 face) (t3FaceEdge2 face) edge ≠ 0 := by
      intro hzero
      have hunit := hcondition.2
      have hzeroKey : gLocalV1SignedCoefficient
          (t3Presentation.gLocalV1CoarseFaceKey A face).edge0
          (t3Presentation.gLocalV1CoarseFaceKey A face).edge1
          (t3Presentation.gLocalV1CoarseFaceKey A face).edge2 edge = 0 := by
        simpa [t3Presentation, identitySplitPresentation] using hzero
      rw [hzeroKey] at hunit
      simp at hunit
    obtain ⟨other, hotherNe, hotherOccurrence⟩ :=
      t3_face_has_other_occurrence face edge hcoeff
    let otherKey := t3Presentation.gLocalV1CoarseFaceKey A other
    have hotherClass : otherKey ∈
        (t3Presentation.gLocalV1InitialState A).coarseFaceClasses := by
      exact (t3Presentation.mem_gLocalV1InitialState_coarseFaceClasses_iff
        A otherKey).2
        ⟨other, t3_face_mem_coarseFaces_of_nonempty A hA other, rfl⟩
    have hotherMem : otherKey ∈
        t3Presentation.gLocalV1CoarseOccurrenceClasses A
          (t3Presentation.gLocalV1InitialState A) edge := by
      exact (t3Presentation.mem_gLocalV1CoarseOccurrenceClasses_iff
        A (t3Presentation.gLocalV1InitialState A) edge otherKey).2
        ⟨hotherClass, hotherOccurrence⟩
    rw [hcondition.1] at hotherMem
    have hkeys := Finset.mem_singleton.mp hotherMem
    exact hotherNe (t3_faceKey_injective A hkeys)
  · intro edge _hedge hnone
    simp [t3Presentation, identitySplitPresentation] at hnone
  · intro key hkey
    obtain ⟨face, hface, rfl⟩ :=
      (t3Presentation.mem_gLocalV1InitialState_coarseFaceClasses_iff A key).1 hkey
    refine ⟨t3FaceEdge0 face,
      t3Presentation.coarseFaceEdge0_mem_gLocalV1CoarseEdges A face hface,
      t3FaceEdge1 face,
      t3Presentation.coarseFaceEdge1_mem_gLocalV1CoarseEdges A face hface,
      ?_⟩
    fin_cases face <;>
      simp [t3Presentation, identitySplitPresentation,
        gLocalV1SignedCoefficient, t3FaceEdge0, t3FaceEdge1, t3FaceEdge2]
  · intro key hkey
    obtain ⟨face, _hface, rfl⟩ :=
      (t3Presentation.mem_gLocalV1InitialState_coarseFaceClasses_iff A key).1 hkey
    fin_cases face <;>
      simp [t3Presentation, identitySplitPresentation,
        t3FaceEdge0, t3FaceEdge2]

/-- Distinct T6 faces have distinct coarse FaceTwin keys in every scope.

Position: fixture-normalization API supporting the structural packet exclusion
for claim (v)(a).  Injectivity is derived from the registered slot-zero face
table and does not assume packet emptiness, an observation, or a label. -/
theorem t6_faceKey_injective (A : Finset (Fin 2)) :
    Function.Injective (t6Presentation.gLocalV1CoarseFaceKey A) := by
  intro left right hequal
  have hedge := congrArg GLocalV1CoarseFaceTwinKey.edge0 hequal
  fin_cases left <;> fin_cases right <;>
    simp [t6Presentation, identitySplitPresentation, t6FaceEdge0] at hedge ⊢

/-- Every T6 face is selected by every nonempty registered target scope.

Position: fixture-normalization API for the T6 packet-exclusion proof in
claim (v)(a).  The premise is exactly nonemptiness of the explicit coarse
target scope; no reducer result or expected observation is supplied. -/
theorem t6_face_mem_coarseFaces_of_nonempty (A : Finset (Fin 2))
    (hA : A.Nonempty) (face : Fin 6) :
    face ∈ t6Presentation.gLocalV1CoarseFaces A := by
  rw [t6Presentation.mem_gLocalV1CoarseFaces_iff_raw]
  obtain ⟨target, htarget⟩ := hA
  refine ⟨target, ?_⟩
  fin_cases face <;> fin_cases target <;>
    simpa [t6Presentation, identitySplitPresentation, t6FaceEdge0,
      t6FaceEdge1, t6FaceEdge2, edgeChart, coarseChartSupport] using htarget

/-- A nonzero T6 signed face coefficient occurs in a second face.

Position: raw finite-incidence lemma excluding singleton coarse occurrences
in the T6 initial state for claim (v)(a).  It uses only the registered six
face rows and does not consume a packet, terminal, or observation value. -/
theorem t6_face_has_other_occurrence (face : Fin 6) (edge : Fin 7)
    (hcoeff : gLocalV1SignedCoefficient
      (t6FaceEdge0 face) (t6FaceEdge1 face) (t6FaceEdge2 face) edge ≠ 0) :
    ∃ other : Fin 6, other ≠ face ∧
      (t6FaceEdge0 other = edge ∨ t6FaceEdge1 other = edge ∨
        t6FaceEdge2 other = edge) := by
  fin_cases face <;> fin_cases edge <;>
    simp [gLocalV1SignedCoefficient,
      t6FaceEdge0, t6FaceEdge1, t6FaceEdge2] at hcoeff ⊢ <;> decide

/-- The T6 initial state has no packet at any nonempty target scope.

Position: primary T6 route-integrity theorem for claim (v)(a).  It applies
the definition-owner packet-family eliminator to raw incidence/support facts;
it neither enumerates assignment spaces nor supplies an expected terminal,
observation, defect, checker result, or semantic label. -/
theorem t6_initial_packet_empty_of_nonempty (A : Finset (Fin 2))
    (hA : A.Nonempty) :
    t6Presentation.gLocalV1PacketVariants A
      (t6Presentation.gLocalV1InitialState A) = ∅ := by
  apply t6Presentation.gLocalV1PacketVariants_eq_empty_of_face_support
  · intro key hkey edge _hedge hcondition
    obtain ⟨face, hface, rfl⟩ :=
      (t6Presentation.mem_gLocalV1InitialState_coarseFaceClasses_iff A key).1 hkey
    have hcoeff : gLocalV1SignedCoefficient
        (t6FaceEdge0 face) (t6FaceEdge1 face) (t6FaceEdge2 face) edge ≠ 0 := by
      intro hzero
      have hunit := hcondition.2
      have hzeroKey : gLocalV1SignedCoefficient
          (t6Presentation.gLocalV1CoarseFaceKey A face).edge0
          (t6Presentation.gLocalV1CoarseFaceKey A face).edge1
          (t6Presentation.gLocalV1CoarseFaceKey A face).edge2 edge = 0 := by
        simpa [t6Presentation, identitySplitPresentation] using hzero
      rw [hzeroKey] at hunit
      simp at hunit
    obtain ⟨other, hotherNe, hotherOccurrence⟩ :=
      t6_face_has_other_occurrence face edge hcoeff
    let otherKey := t6Presentation.gLocalV1CoarseFaceKey A other
    have hotherClass : otherKey ∈
        (t6Presentation.gLocalV1InitialState A).coarseFaceClasses := by
      exact (t6Presentation.mem_gLocalV1InitialState_coarseFaceClasses_iff
        A otherKey).2
        ⟨other, t6_face_mem_coarseFaces_of_nonempty A hA other, rfl⟩
    have hotherMem : otherKey ∈
        t6Presentation.gLocalV1CoarseOccurrenceClasses A
          (t6Presentation.gLocalV1InitialState A) edge := by
      exact (t6Presentation.mem_gLocalV1CoarseOccurrenceClasses_iff
        A (t6Presentation.gLocalV1InitialState A) edge otherKey).2
        ⟨hotherClass, hotherOccurrence⟩
    rw [hcondition.1] at hotherMem
    have hkeys := Finset.mem_singleton.mp hotherMem
    exact hotherNe (t6_faceKey_injective A hkeys)
  · intro edge _hedge hnone
    simp [t6Presentation, identitySplitPresentation] at hnone
  · intro key hkey
    obtain ⟨face, hface, rfl⟩ :=
      (t6Presentation.mem_gLocalV1InitialState_coarseFaceClasses_iff A key).1 hkey
    refine ⟨t6FaceEdge0 face,
      t6Presentation.coarseFaceEdge0_mem_gLocalV1CoarseEdges A face hface,
      t6FaceEdge1 face,
      t6Presentation.coarseFaceEdge1_mem_gLocalV1CoarseEdges A face hface,
      ?_⟩
    fin_cases face <;>
      simp [t6Presentation, identitySplitPresentation,
        gLocalV1SignedCoefficient, t6FaceEdge0, t6FaceEdge1, t6FaceEdge2]
  · intro key hkey
    obtain ⟨face, _hface, rfl⟩ :=
      (t6Presentation.mem_gLocalV1InitialState_coarseFaceClasses_iff A key).1 hkey
    fin_cases face <;>
      simp [t6Presentation, identitySplitPresentation,
        t6FaceEdge0, t6FaceEdge2]

/-- T3 has no initial reduction packet at target zero.

Position: raw reducer firing fact for the observation fast path in claim
(v)(a).  It computes the generic packet kernel from the registered tables and
does not supply a terminal, observation, or label. -/
theorem t3_targetZero_initial_packet_empty :
    t3Presentation.gLocalV1PacketVariants targetZero
      (t3Presentation.gLocalV1InitialState targetZero) = ∅ := by
  exact t3_initial_packet_empty_of_nonempty targetZero (by decide)

/-- T3 has no initial reduction packet at target one.

Position: raw reducer firing fact for the observation fast path in claim
(v)(a).  It computes the generic packet kernel from the registered tables and
does not supply a terminal, observation, or label. -/
theorem t3_targetOne_initial_packet_empty :
    t3Presentation.gLocalV1PacketVariants targetOne
      (t3Presentation.gLocalV1InitialState targetOne) = ∅ := by
  exact t3_initial_packet_empty_of_nonempty targetOne (by decide)

/-- T3 has no initial reduction packet at the full target.

Position: raw reducer firing fact for the observation fast path in claim
(v)(a).  It computes the generic packet kernel from the registered tables and
does not supply a terminal, observation, or label. -/
theorem t3_targetFull_initial_packet_empty :
    t3Presentation.gLocalV1PacketVariants targetFull
      (t3Presentation.gLocalV1InitialState targetFull) = ∅ := by
  exact t3_initial_packet_empty_of_nonempty targetFull (by decide)

/-- T6 has no initial reduction packet at target zero.

Position: raw reducer firing fact for the observation fast path in claim
(v)(a).  It computes the generic packet kernel from the registered tables and
does not supply a terminal, observation, or label. -/
theorem t6_targetZero_initial_packet_empty :
    t6Presentation.gLocalV1PacketVariants targetZero
      (t6Presentation.gLocalV1InitialState targetZero) = ∅ := by
  exact t6_initial_packet_empty_of_nonempty targetZero (by decide)

/-- T6 has no initial reduction packet at target one.

Position: raw reducer firing fact for the observation fast path in claim
(v)(a).  It computes the generic packet kernel from the registered tables and
does not supply a terminal, observation, or label. -/
theorem t6_targetOne_initial_packet_empty :
    t6Presentation.gLocalV1PacketVariants targetOne
      (t6Presentation.gLocalV1InitialState targetOne) = ∅ := by
  exact t6_initial_packet_empty_of_nonempty targetOne (by decide)

/-- T6 has no initial reduction packet at the full target.

Position: raw reducer firing fact for the observation fast path in claim
(v)(a).  It computes the generic packet kernel from the registered tables and
does not supply a terminal, observation, or label. -/
theorem t6_targetFull_initial_packet_empty :
    t6Presentation.gLocalV1PacketVariants targetFull
      (t6Presentation.gLocalV1InitialState targetFull) = ∅ := by
  exact t6_initial_packet_empty_of_nonempty targetFull (by decide)

/-! The companion `GLocalV1T3T6Observation` module derives the independent
full observation normal forms from these raw fixtures.  Both semantic label
firings remain deferred to the next proof-obligation cycle. -/

end GLocalV1T3T6Witnesses
end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
